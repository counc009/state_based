let uid = Ast.uid
type uid = Ast.uid

type id = Ast.id

module Interp(Ast : Ast.Ast_Defs) = struct
  open Ast

  let type_of_val (v : value) : typ =
    match v with
    | Unknown (_, t) -> t
    | Literal (_, p) -> Primitive p
    | Function (_, _, t) -> t
    | Pair (_, _, t) -> t
    | Constructor (n, _, _) -> Named n
    | Struct (s, _) -> Struct s
    | ListVal (n, _) -> Named n

  let list_like (n : namedTy) : typ option =
    let (nil, cons) = namedTyDef n
    in if not (isUnit nil) then None
    else match cons with
      | Product (hd, Named tl) when tl = n -> Some hd
      | _ -> None

  type env = (value * typ) VariableMap.t

  let rec eval_expr (e : expr) (env : env) : (value * typ, string) result =
    match e with
    | Function (f, exp) ->
        Result.bind (eval_expr exp env) (fun (v, t) ->
          let (argTy, retTy, interp) = funcDef f
          in if t <> argTy
            then Error "Type error, argument type mismatch"
            else
              match interp v with
              | Reduced w -> Ok (w, retTy)
              | Stuck     -> Ok (Function (f, v, retTy), retTy)
              | Err msg   -> Error msg)
    | Literal l ->
        let p = literalTyp l
        in Ok (Literal (l, p), Primitive p)
    | Variable v ->
        begin match VariableMap.find_opt v env with
        | None -> Error "Undefined variable"
        | Some v -> Ok v
        end
    | Pair (x, y) ->
        begin match eval_expr x env, eval_expr y env with
        | Ok (x, tx), Ok (y, ty)
          -> let t : typ = Product (tx, ty) in Ok (Pair (x, y, t), t)
        | Error m, Error n -> Error (m ^ "\n" ^ n)
        | Error m, Ok _ -> Error m
        | Ok _, Error n -> Error n
        end

  let construct_equals v w : (value, string) result =
    let tv = type_of_val v
    in let tw = type_of_val w
    in if tv <> tw
      then Error "Type error, cannot equate values of different types"
      else
        let equals = equality_func tv
        in let (_, retTy, _) = funcDef equals
        in Ok (
        Function (
          equals,
          Pair (v, w, Product (tv, tw)),
          retTy))

  let fieldMap_map_result (f : 'a -> ('b, 'e) result) (m : 'a FieldMap.t)
    : ('b FieldMap.t, 'e) result
    = FieldMap.fold
        (fun k v res -> Result.bind res (fun new_map ->
          Result.bind (f v) (fun new_v ->
            Ok (FieldMap.add k new_v new_map))))
        m
        (Ok FieldMap.empty)

  let variableMap_map_result (f : 'a -> ('b, 'e) result) (m : 'a VariableMap.t)
    : ('b VariableMap.t, 'e) result
    = VariableMap.fold
        (fun k v res -> Result.bind res (fun new_map ->
          Result.bind (f v) (fun new_v ->
            Ok (VariableMap.add k new_v new_map))))
        m
        (Ok VariableMap.empty)

  module ValueOrder : Map.OrderedType with type t = value = struct
    type t = value
    let compare : value -> value -> int = compare
  end
  module ValueMap : (Map.S with type key = value) = Map.Make(ValueOrder)

  (* States are made up of maps of qualifiers. For elements, we store the
   * element, value, and whether or not it is negated (true = negated) as the
   * key and the value is qualifiers applied to it. For attributes, the key is
   * just the attribute and whether it is negated and this maps to the value and
   * any qualifiers applied to it. *)
  module ElementOrder : Map.OrderedType with type t = element * value = struct
    type t = element * value
    let compare : t -> t -> int = compare
  end
  module ElementMap : (Map.S with type key = element * value)
    = Map.Make(ElementOrder)

  module AttributeOrder : Map.OrderedType with type t = attribute = struct
    type t = attribute
    let compare : t -> t -> int = compare
  end
  module AttributeMap : (Map.S with type key = attribute)
    = Map.Make(AttributeOrder)

  type element_result = Negated | Positive of state
  and state = State of element_result ElementMap.t * value AttributeMap.t

  let empty_state = State (ElementMap.empty, AttributeMap.empty)

  type loop_info = AllUnknown of uid | AllKnown of value | LastKnown of uid * value

  type interp_state = {
    init    : state;
    final   : state;
    (* Map between values and the loop variable over that value *)
    loops   : loop_info ValueMap.t;
    (* Map between values and its boolean value *)
    bools   : bool ValueMap.t;
    (* Map between values and its constructor value (true = L) *)
    constrs : (bool * value) ValueMap.t;
  }

  let init_interp_state = {
    init    = empty_state;
    final   = empty_state;
    loops   = ValueMap.empty;
    bools   = ValueMap.empty;
    constrs = ValueMap.empty;
  }

  type interp_res =
    | Err     of string
    | Success of interp_state
    | Both    of interp_res * interp_res

  (* Add the second state to the first state *)
  let rec add_states (State (el, at)) (State (em, ar)) : state =
    let new_attrs =
      AttributeMap.merge (fun _attr orig added ->
        match added with
        | Some v -> Some v
        | None -> orig)
        at ar
    in let new_elems =
      ElementMap.merge (fun _elem orig added ->
        match orig, added with
        | None, None -> None
        | None, Some added -> Some added
        | Some orig, None -> Some orig
        | Some Negated, Some added -> Some added
        | Some _, Some Negated -> Some Negated
        | Some (Positive orig), Some (Positive added) ->
            Some (Positive (add_states orig added)))
        el em
    in State (new_elems, new_attrs)

  type qualifier = Attribute  of attribute * value
                 | Element    of element   * value * state
                 | NotElement of element   * value

  let add_qual (q : qualifier) (State (els, ats) : state) : state =
    match q with
    | Attribute (attr, v) ->
        State (els, AttributeMap.add attr v ats)
    | NotElement (elem, v) ->
        State (ElementMap.add (elem, v) Negated els, ats)
    | Element (elem, v, nested) ->
        let updated =
          ElementMap.update (elem, v)
            (fun cur ->
              let s =
                match cur with
                | None | Some Negated -> empty_state
                | Some (Positive s) -> s
              in Some (Positive (add_states s nested)))
            els
        in State (updated, ats)

  let rec eval_qual (q : qual) (env : env) : (qualifier, string) result =
    match q with
    | Attribute (attr, exp) ->
        Result.bind (eval_expr exp env) (fun (v, _) ->
          Ok (Attribute (attr, v)))
    | Element (elem, exp, q) ->
        Result.bind (eval_expr exp env) (fun (v, _) ->
          match q with
          | None -> Ok (Element (elem, v, empty_state))
          | Some q ->
              Result.bind (eval_qual q env) (fun q ->
                Ok (Element (elem, v, add_qual q empty_state))))
    | NotElement (elem, exp) ->
        Result.bind (eval_expr exp env) (fun (v, _) ->
          Ok (NotElement (elem, v)))

  (* A type representing attempting to find some value in a structure where we
   * may find it, know that it cannot exist, or may not find it and either be
   * able to add it "easily" or by creating a substantial structure to add it *)
  type ('a, 'b) find = Located of 'a
                     | NotContained
                     | Added   of 'a * 'b
                     | Created of 'a * 'b

  let get_attribute (a : attr) (s : interp_state) (env : env)
    : (value * interp_state, string) result =
    let rec attr_to_state (a : attr) : (value * state, string) result =
      match a with
      | AttrAccess a ->
          let v : value = Unknown (Val (uid ()), attributeDef a)
          in Ok (v, add_qual (Attribute (a, v)) empty_state)
      | OnElement (el, ex, at) ->
          Result.bind (eval_expr ex env) (fun (v, _) ->
            Result.bind (attr_to_state at) (fun (atv, s) ->
              Ok (atv, add_qual (Element (el, v, s)) empty_state)))
    in let rec find_in_state (a : attr) (State (els, ats))
      : ((value, state) find, string) result =
      match a with
      | AttrAccess a ->
          begin match AttributeMap.find_opt a ats with
          | Some v -> Ok (Located v)
          | None ->
              let v : value = Unknown (Val (uid ()), attributeDef a)
              in Ok (Added (v, State (els, AttributeMap.add a v ats)))
          end
      | OnElement (el, ex, at) ->
          Result.bind (eval_expr ex env) (fun (v, _) ->
            match ElementMap.find_opt (el, v) els with
            | None ->
                Result.bind (attr_to_state at) (fun (res, nested) ->
                  Ok (Created (res,
                    State (ElementMap.add (el, v) (Positive nested) els, ats))))
            | Some Negated -> Ok NotContained
            | Some (Positive s) ->
                match find_in_state at s with
                | Error msg -> Error msg
                | Ok NotContained -> Ok NotContained
                | Ok (Located v) -> Ok (Located v)
                | Ok (Added (res, st)) ->
                    let new_els = ElementMap.add (el, v) (Positive st) els
                    in Ok (Added (res, State (new_els, ats)))
                | Ok (Created (res, st)) ->
                    let new_els = ElementMap.add (el, v) (Positive st) els
                    in Ok (Created (res, State (new_els, ats))))
    in match find_in_state a s.final with
    | Error msg -> Error msg
    (* NotContained means that one of the elements the attribute is on was
     * negated in the final state, meaning this attribute does not have a value *)
    | Ok NotContained -> Error "Attribute does not exist"
    | Ok (Located v) -> Ok (v, s)
    | Ok (Added (v, new_final)) ->
        (* We prefer to add a value for an attribute on the initial state
         * rather than the final state since that gives us a source of the
         * value *)
        begin match find_in_state a s.init with
        | Ok (Located v) -> Ok (v, s)
        | Ok (Added (v, new_init)) ->
            Ok (v, { init = new_init; final = s.final; loops = s.loops;
                     bools = s.bools; constrs = s.constrs })
        (* If the value cannot be contained in the initial state, would require
         * creating an element, or we ran into some kind of error (which would
         * be unexpected) we just add the attribute in the final state *)
        (* NOTE: We prefer to Add rather than Create since this may represent a
         * situation where we have added an element and are now accesssing
         * an unspecified attribute *)
        | _ -> Ok (v, { init = s.init; final = new_final; loops = s.loops;
                        bools = s.bools; constrs = s.constrs })
        end
    (* We cannot create elements in the final state but we can try the initial
     * state *)
    | Ok (Created (_, _)) ->
        begin match find_in_state a s.init with
        | Ok (Located v) -> Ok (v, s)
        | Ok NotContained -> Error "Attribute does not exist"
        | Ok (Added (v, new_init)) | Ok (Created (v, new_init)) ->
            Ok (v, { init = new_init; final = s.final; loops = s.loops;
                     bools = s.bools; constrs = s.constrs })
        (* This would be unexpected *)
        | Error msg -> Error msg
        end

  (* Either returns whether or not the element is in the state (Either.Left) or
   * new initial states that assume the element does and does not exist,
   * respectively (Either.Right) *)
  let get_element (e : elem) (s : interp_state) (env : env)
    (k : bool -> interp_state -> interp_res)
    : (interp_res, string) result =
    let rec find_in_state (e : elem) (State (els, _))
      : (bool option, string) result =
      match e with
      | Element (el, ex) ->
          Result.bind (eval_expr ex env) (fun (v, _) ->
            match ElementMap.find_opt (el, v) els with
            | Some (Positive _) -> Ok (Some true)
            | Some Negated -> Ok (Some false)
            | None -> Ok None)
      | OnElement (el, ex, e) ->
          Result.bind (eval_expr ex env) (fun (v, _) ->
            match ElementMap.find_opt (el, v) els with
            | None -> Ok None
            | Some Negated -> Ok (Some false)
            | Some (Positive s) -> find_in_state e s)
    in let rec states_from_elem (e : elem)
      (k : bool -> state -> interp_res) : (interp_res, string) result =
      match e with
      | Element (el, ex) ->
          Result.bind (eval_expr ex env) (fun (v, _) ->
            let state_with =
              add_qual (Element (el, v, empty_state)) empty_state
            in let state_without =
              add_qual (NotElement (el, v)) empty_state
            in Ok (Both (k true state_with, k false state_without)))
      | OnElement (el, ex, e) ->
          Result.bind (eval_expr ex env) (fun (v, _) ->
            let state_without =
              add_qual (NotElement (el, v)) empty_state
            in let res_e =
              states_from_elem e
                (fun b s -> k b (add_qual (Element (el, v, s)) empty_state))
            in Result.bind res_e (fun res_e ->
              Ok (Both (res_e, k false state_without))))
    in let rec find_or_add (e : elem) (State (els, ats))
      (k : bool -> state -> interp_res) : (interp_res, string) result =
      match e with
      | Element (el, ex) ->
          Result.bind (eval_expr ex env) (fun (v, _) ->
            match ElementMap.find_opt (el, v) els with
            | Some (Positive _) -> Ok (k true (State (els, ats)))
            | Some Negated -> Ok (k false (State (els, ats)))
            | None ->
                let els_with =
                  ElementMap.add (el, v) (Positive empty_state) els
                in let els_without =
                  ElementMap.add (el, v) Negated els
                in Ok (Both (k true (State (els_with, ats)),
                             k false (State (els_without, ats)))))
      | OnElement (el, ex, e) ->
          Result.bind (eval_expr ex env) (fun (v, _) ->
            match ElementMap.find_opt (el, v) els with
            | Some Negated -> Ok (k false (State (els, ats)))
            | Some (Positive s) ->
                find_or_add e s (fun b new_s ->
                  let new_els = ElementMap.add (el, v) (Positive new_s) els
                  in k b (State (new_els, ats)))
            | None ->
                let states_res =
                  states_from_elem e (fun b s ->
                    let new_els = ElementMap.add (el, v) (Positive s) els
                    in k b (State (new_els, ats)))
                in Result.bind states_res (fun states_res ->
                  let els_without = ElementMap.add (el, v) Negated els
                  in Ok (Both (states_res, k false (State (els_without, ats))))))
    (* First check if we can resolve this question based on the final state *)
    in match find_in_state e s.final with
    | Error msg -> Error msg
    | Ok (Some b) -> Ok (k b s)
    | Ok None ->
        (* If not, we'll use the initial state and either find out or try all
         * the options *)
        find_or_add e s.init (fun b new_init ->
          let new_state = {
            init = new_init; final = s.final; loops = s.loops;
            bools = s.bools; constrs = s.constrs }
          in k b new_state)

  (* Given an element and the current state, evaluates the element and returns
   * a function which given a new state resets the specified element in the
   * final state to the same as the initial state.
   * This is used for the Localize construct, and we only modify the final
   * state so that any changes that occured during localization are undone
   * but any inferred information about the initial state are not (since the
   * initial version of the localized state is the current state of the state
   * before localization). *)
  let make_elem_reset (el : element) (ex : expr) (s : interp_state) (env : env)
    : (interp_state -> interp_state, string) result =
    let State (els, _) = s.final
    in let change_final (f : state -> state) (s : interp_state) =
      let { init; final; loops; bools; constrs } = s
      in { init; final = f final; loops; bools; constrs }
    in Result.bind (eval_expr ex env) (fun (v, _) ->
        match ElementMap.find_opt (el, v) els with
        | None ->
            Ok (change_final (fun (State (els, ats)) ->
              State (ElementMap.remove (el, v) els, ats)))
        | Some b ->
            Ok (change_final (fun (State (els, ats)) ->
              State (ElementMap.add (el, v) b els, ats))))

  let replace_loopvar_value (v : value) (uid : uid) : value =
    let rec helper (v : value) : value =
      match v with
      | Unknown (Loop x, elemTy) when x = uid -> Unknown (Val x, elemTy)
      | Function (f, v, t) -> Function (f, helper v, t)
      | Pair (x, y, t) -> Pair (helper x, helper y, t)
      | Constructor (n, b, v) -> Constructor (n, b, helper v)
      | Struct (s, r) -> Struct (s, FieldMap.map helper r)
      (* ListVal are not modified because they are allowed to contain loop
       * variables *)
      | _ -> v
    in helper v

  let replace_loopvar (s : interp_state) (env : env) (uid : uid)
    : interp_state * env =
    let rec contains_loopvar (v : value) : bool =
      match v with
      | Unknown (Loop x, _) -> x = uid
      | Function (_, v, _) -> contains_loopvar v
      | Pair (x, y, _) -> contains_loopvar x || contains_loopvar y
      | Constructor (_, _, v) -> contains_loopvar v
      | Struct (_, r) -> FieldMap.exists (fun _ v -> contains_loopvar v) r
      (* ListVal are not checked since they are lists not individual values *)
      | _ -> false
    in let rec replace_state (State (els, ats) : state) : state =
      let replace_els (els : element_result ElementMap.t)
        : element_result ElementMap.t =
        ElementMap.mapi
          (fun (_, v) st ->
            match st with
            | Negated -> Negated
            | Positive s ->
                if contains_loopvar v
                then Positive s
                else Positive (replace_state s))
          els
      in let replace_ats (ats : value AttributeMap.t)
        : value AttributeMap.t =
        AttributeMap.map (fun v -> replace_loopvar_value v uid) ats
      in State (replace_els els, replace_ats ats)
    in ({ init = replace_state s.init; final = replace_state s.final;
          loops = s.loops; bools = s.bools; constrs = s.constrs },
        VariableMap.map (fun (v, t) -> (replace_loopvar_value v uid, t)) env)

  let rec substitute_unknown (u : id) (v : value) (s : interp_state) (env : env)
    (k : interp_state -> env -> (interp_res, string) result)
    (merge : interp_res -> interp_res -> interp_res)
    : (interp_res, string) result =
    let rec subst_in_value (w : value) : (value, string) result =
      match w with
      | Unknown (w, _) when u = w -> Ok v
      | Unknown (_, _) | Literal (_, _) -> Ok w
      | Function (f, v, t) ->
          Result.bind (subst_in_value v) (fun new_v ->
            let (_, _, f_def) = funcDef f
            in match f_def new_v with
            | Reduced w -> Ok w
            | Stuck -> Ok (Function (f, new_v, t))
            | Err msg -> Error msg)
      | Pair (x, y, t) ->
          Result.bind (subst_in_value x) (fun new_x ->
            Result.bind (subst_in_value y) (fun new_y ->
              Ok (Pair (new_x, new_y, t))))
      | Constructor (n, c, v) ->
          Result.bind (subst_in_value v) (fun new_v ->
            Ok (Constructor (n, c, new_v)))
      | Struct (t, r) ->
          Result.bind (fieldMap_map_result subst_in_value r) (fun new_r ->
            Ok (Struct (t, new_r)))
      (* Unlike substituting loop variables where we skip listvals we do handle
       * listvals here since they may contain unknown values that we want to
       * eliminate *)
      | ListVal (n, w) ->
          Result.bind (subst_in_value w) (fun new_w ->
            Ok (ListVal (n, new_w)))
    in let rec subst_in_state (s : state) : (state, string) result =
      match s with
      | State (elems, attrs) ->
          let with_elems =
            ElementMap.fold
              (fun (el, v) s new_state ->
                Result.bind new_state (fun new_state ->
                  Result.bind (subst_in_value v) (fun new_v ->
                    match s with
                    | Negated -> Ok (add_qual (NotElement (el, new_v)) new_state)
                    | Positive s ->
                        Result.bind (subst_in_state s) (fun new_s ->
                          Ok (add_qual (Element (el, new_v, new_s)) new_state)))))
              elems (Ok empty_state)
          in let with_attrs =
            Result.bind with_elems (fun with_elems ->
              AttributeMap.fold
                (fun attr v new_state ->
                  Result.bind new_state (fun new_state ->
                    Result.bind (subst_in_value v) (fun new_v ->
                      Ok (add_qual (Attribute (attr, new_v)) new_state))))
                attrs (Ok with_elems))
          in with_attrs
    in let new_env : (env, string) result =
      variableMap_map_result
        (fun (v, t) -> Result.bind (subst_in_value v) (fun v -> Ok (v, t)))
        env
    in let new_init = subst_in_state s.init
    in let new_final = subst_in_state s.final
    in let new_loops =
      ValueMap.fold (fun lst loop new_loops ->
        Result.bind new_loops (fun new_loops ->
          let new_lst = subst_in_value lst
          in let new_loop =
            match loop, u with
            | AllUnknown i, Loop j when i = j -> Ok (AllKnown v)
            | AllUnknown i, Val j when i = j -> Ok (LastKnown (i, v))
            | AllUnknown _, _ -> Ok loop
            | AllKnown w, _ ->
                Result.bind (subst_in_value w) (fun w -> Ok (AllKnown w))
            | LastKnown (i, _w), Loop j when i = j ->
                (* TODO: Should unify w and v *) Ok (AllKnown v)
            | LastKnown  (i, w), _ ->
                Result.bind (subst_in_value w) (fun w -> Ok (LastKnown (i, w)))
          in Result.bind new_loop (fun new_loop ->
              Result.bind new_lst (fun new_lst ->
                match ValueMap.find_opt new_lst new_loops with
                | None ->
                    Ok (ValueMap.add new_lst new_loop new_loops)
                | Some _l -> (* TODO: Should unify l and new_loop *)
                    Ok new_loops))))
        s.loops
        (Ok ValueMap.empty)
    (* We don't add bools and constrs manually, we use addConstraint *)
    in let partial_state =
      Result.bind new_init (fun new_init ->
        Result.bind new_final (fun new_final ->
          Result.bind new_loops (fun new_loops ->
            Result.bind new_env (fun new_env ->
              Ok ({ init = new_init; final = new_final; loops = new_loops;
                    bools = ValueMap.empty; constrs = ValueMap.empty },
                  new_env)))))
    in let add_bools =
      ValueMap.fold
        (fun old_v constr k state env -> 
          Result.bind (subst_in_value old_v) (fun new_v ->
            addConstraint new_v (IsBool constr) state env k merge))
        s.bools
        k
    in let add_constrs =
      ValueMap.fold
        (fun old_v (cb, cv) k state env -> 
          Result.bind (subst_in_value old_v) (fun new_v ->
            addConstraint new_v (IsConstructor (cb, cv)) state env k merge))
        s.constrs
        add_bools
    in Result.bind partial_state (fun (s, env) -> add_constrs s env)

  and addConstraint (v : value) (c : constr) (s : interp_state) (env : env)
    (k : interp_state -> env -> (interp_res, string) result)
    (merge : interp_res -> interp_res -> interp_res)
    : (interp_res, string) result =
    let addConstraintBasic (v : value) (c : constr) (s : interp_state)
      (env : env) (k : interp_state -> env -> (interp_res, string) result) =
      match c with
      | IsBool b ->
          let new_state = {
            init = s.init; final = s.final; loops = s.loops;
            bools = ValueMap.add v b s.bools;
            constrs = s.constrs }
          in k new_state env
      | IsConstructor (which, c) ->
          let new_state = {
            init = s.init; final = s.final; loops = s.loops;
            bools = s.bools;
            constrs = ValueMap.add v (which, c) s.constrs }
          in k new_state env
      | IsEqual w ->
          (* TODO: Ideally we would track a congruence closure data structure
           * (i.e., an e-graph) but that's very complicated as we'd need a
           * pure or persistent e-graph implementation *)
          Result.bind (construct_equals v w) (fun equality_vw ->
            Result.bind (construct_equals w v) (fun equality_wv ->
              let new_state = {
                init = s.init; final = s.final; loops = s.loops;
                bools = ValueMap.add equality_vw true
                          (ValueMap.add equality_wv true s.bools);
                constrs = s.constrs }
              in k new_state env))

    in let checkValue =
      match c with
      | IsBool b ->
          begin match asTruth v with
          | Some c when b = c -> Some (k s env)
          | Some _ -> Some (Error "Incompatible constraints")
          | None ->
              match ValueMap.find_opt v s.bools with
              | Some c when b = c -> Some (k s env)
              | Some _ -> Some (Error "Incompatible constraints")
              | None -> None
          end
      | IsConstructor (which, b) ->
          begin match v with
          | Constructor (_, c, x) when c = which ->
              Some (addConstraint x (IsEqual b) s env k merge)
          | Constructor (_, _, _) -> Some (Error "Incompatible constraints")
          | _ ->
              match ValueMap.find_opt v s.constrs with
              | Some (c, x) when c = which ->
                  Some (addConstraint x (IsEqual b) s env k merge)
              | Some (_, _) -> Some (Error "Incompatible constraints")
              | None -> None
          end
      | IsEqual w ->
          if v = w
          then Some (k s env)
          else
            match construct_equals v w with
            | Error msg -> Some (Error msg)
            | Ok equality_check ->
              match ValueMap.find_opt equality_check s.bools with
              | Some true -> Some (k s env)
              | Some false -> Some (Error "Incompatible constraints")
              | None ->
                match v, w with
                | Unknown (id, _), _ ->
                    Some (substitute_unknown id w s env k merge)
                | _, Unknown (id, _) ->
                    Some (substitute_unknown id v s env k merge)
                (* TODO: Is it fair to assume literals must be syntactically equal? *)
                | Literal (_, _), Literal (_, _) ->
                    Some (Error "Incompatible constraints")
                | Pair (a, b, _), Pair (x, y, _) ->
                    Some (addConstraint a (IsEqual x) s env
                      (fun s env ->
                        addConstraint b (IsEqual y) s env k merge)
                      merge)
                | Constructor (_, a, b), Constructor (_, x, y) ->
                    if a = x
                    then
                      Some (addConstraint b (IsEqual y) s env k merge)
                    else Some (Error "Incompatiable constraints")
                | Struct (_, x), Struct (_, y) ->
                    let merged =
                      FieldMap.merge (fun _f x y ->
                        match x, y with
                        | Some x, Some y -> Some (Ok (x, y))
                        | None, None -> None
                        | _, _ -> Some (Error "Incompatible constraints"))
                        x y
                    in Some (FieldMap.fold (fun _f vals k s env ->
                        Result.bind vals (fun (x, y) ->
                          addConstraint x (IsEqual y) s env k merge))
                        merged k s env)
                | ListVal (_, x), ListVal (_, y) ->
                    (* TODO: Is this correct? *)
                    Some (addConstraint x (IsEqual y) s env k merge)
                (* TODO: Is there more we can do here? *)
                | Constructor (_, _, _), ListVal (_, _) -> None
                | ListVal (_, _), Constructor (_, _, _) -> None
                (* Try to simplify function stuff below *)
                | Function (_, _, _), _ -> None
                | _, Function (_, _, _) ->
                    (* Swap so that we can simplify the function *)
                    Some (addConstraint w (IsEqual v) s env k merge)
                | _, _ -> Some (Error "Incompatible constraints")
    in match checkValue with
    | Some res -> res
    | None ->
        match v with
        | Unknown (id, typ) ->
            let new_val =
              match c with
              | IsBool b -> Ok (boolAsValue b)
              | IsConstructor (which, c) ->
                  begin match typ with
                  | Named nm -> Ok (Constructor (nm, which, c))
                  | _ -> Error "Invalid type for constructor"
                  end
              | IsEqual w -> Ok w
            in begin match new_val with
            | Ok new_val -> substitute_unknown id new_val s env k merge
            | Error msg -> Error msg
            end
        | Function (f, arg, _) ->
            begin match reduceFuncConstraint f arg c with
            | Unreducible -> addConstraintBasic v c s env k
            | Reducible options ->
                List.fold_left
                  (fun total_res cs ->
                    let this_res : (interp_res, string) result =
                      List.fold_left
                        (fun k c s env ->
                          match c with
                          | IsBool (v, b) ->
                              addConstraint v (IsBool b) s env k merge
                          | IsConstructor (v, (which, arg)) ->
                              addConstraint v (IsConstructor (which, arg))
                                s env k merge
                          | IsEqual (x, y) ->
                              addConstraint x (IsEqual y) s env k merge)
                        k
                        cs
                        s
                        env
                    in match total_res, this_res with
                    | Error _, _ -> this_res
                    | _, Error _ -> total_res
                    | Ok total, Ok this -> Ok (merge total this))
                  (Error "Unsatisfiable function constraint reduction")
                  options
            end
        | _ -> addConstraintBasic v c s env k

  let rec interpret (p : stmt) (s : interp_state) (env : env)
    (cont  : interp_state -> env -> interp_res)
    (yield : interp_state -> env -> value * typ -> interp_res)
    (ret   : interp_state -> env -> value * typ -> interp_res)
    (raise : interp_state -> env -> value * typ -> interp_res) : interp_res =
    match p with
    | Pass -> cont s env
    | Seq (x, y) ->
        interpret x s env
          (fun s env -> interpret y s env cont yield ret raise)
          yield
          ret
          raise
    | Action (var, a, e) ->
        begin match eval_expr e env with
        | Error msg -> Err msg
        | Ok (v, t) ->
            let (in_var, in_ty, ret_ty, body) = actionDef a
            in if t <> in_ty
            then Err "Incorrect argument type for action"
            else
              interpret body s (VariableMap.singleton in_var (v, t))
                (fun _ _ -> Err "No return from action, continued instead")
                (fun _ _ _ -> Err "No return from action, yielded instead")
                (fun s _ (r, t) ->
                  if t <> ret_ty
                  then Err "Incorrect return type from action"
                  else cont s (VariableMap.add var (r, t) env))
                (fun s _ e -> raise s env e)
        end
    | Assign (var, e) ->
        begin match eval_expr e env with
        | Error msg -> Err msg
        | Ok v -> cont s (VariableMap.add var v env)
        end
    | Add qual ->
        begin match eval_qual qual env with
        | Error msg -> Err msg
        | Ok q ->
            let new_final = add_qual q s.final
            in let new_state = {
              init = s.init; final = new_final; loops = s.loops;
              bools = s.bools; constrs = s.constrs }
            in cont new_state env
        end
    | Get (var, attr) ->
        begin match get_attribute attr s env with
        | Error msg -> Err msg
        | Ok (v, new_state) ->
            let new_env = VariableMap.add var (v, type_of_val v) env
            in cont new_state new_env
        end
    | Contains (elem, thn, els) ->
        let get_res =
          get_element elem s env (fun b new_s ->
            interpret (if b then thn else els) new_s env cont yield ret raise)
        in begin match get_res with
        | Error msg -> Err msg
        | Ok res -> res
        end
    (* For both cond and match we try to reduce the expression to a concrete
     * value that we can branch on. However, if it cannot reduce to such an
     * expression then we try both possible options (which involves
     * interacting with the constraints of the current state) *)
    | Cond (c, thn, els) ->
        begin match eval_expr c env with
        | Error msg -> Err msg
        | Ok (v, t) ->
            if not (isTruthType t)
            then Err "Condition is not truthy"
            else
              match asTruth v with
              | Some true  -> interpret thn s env cont yield ret raise
              | Some false -> interpret els s env cont yield ret raise
              | None ->
                  let true_res =
                    addConstraint v (IsBool true) s env
                      (fun s env ->
                        Ok (interpret thn s env cont yield ret raise))
                      (* If this is an existential condition, then use Either
                       * here instead of Both *)
                      (fun x y -> Both (x, y))
                  in let false_res =
                    addConstraint v (IsBool false) s env
                      (fun s env ->
                        Ok (interpret els s env cont yield ret raise))
                      (fun x y -> Both (x, y))
                  (* true_res and false_res can be Error iff adding the
                   * constraint fails, meaning it is inconsistent. If only one
                   * fails we can safely ignore it *)
                  in match true_res, false_res with
                  | Ok true_res, Ok false_res -> Both (true_res, false_res)
                  | Ok res, Error _ | Error _, Ok res -> res
                  | Error m, Error n -> Err (m ^ "\n" ^ n)
        end
    | Match (expr, var, left, right) ->
        begin match eval_expr expr env with
        | Error msg -> Err msg
        | Ok (v, t) ->
            match t with
            | Named n ->
                begin match v with
                | Constructor (_, b, v) ->
                    let t = (if b then fst else snd) (namedTyDef n)
                    in let new_env = VariableMap.add var (v, t) env
                    in interpret (if b then left else right) s new_env
                          cont yield ret raise
                (* The value cannot be evaluated sufficiently so try both *)
                | _ ->
                    let (type_left, type_right) = namedTyDef n
                    in let val_left = Unknown (Val (uid ()), type_left)
                    in let val_right = Unknown (Val (uid ()), type_right)
                    in let env_left =
                      VariableMap.add var (val_left, type_left) env
                    in let env_right =
                      VariableMap.add var (val_right, type_right) env
                    in let left_res =
                      addConstraint v (IsConstructor (true, val_left))
                        s env_left
                        (fun s env ->
                          Ok (interpret left s env cont yield ret raise))
                        (fun x y -> Both (x, y))
                    in let right_res =
                      addConstraint v (IsConstructor (false, val_right))
                        s env_right
                        (fun s env ->
                          Ok (interpret right s env cont yield ret raise))
                        (fun x y -> Both (x, y))
                    in match left_res, right_res with
                    | Ok left_res, Ok right_res -> Both (left_res, right_res)
                    | Ok res, Error _ | Error _, Ok res -> res
                    | Error m, Error n -> Err (m ^ "\n" ^ n)
                end
            | _ -> Err "Cannot match over non-named type"
        end
    | ForEach (var, resTy, lst, elemVar, body) ->
        begin match eval_expr lst env with
        | Error msg -> Err msg
        | Ok (v, t) ->
            match t with
            | Named n ->
                begin match list_like n with
                | None -> Err "Cannot loop over non list-like type"
                | Some elemTy ->
                    let rec process_foreach (lst : value) (s : interp_state)
                      (env : env)
                      (cont : value -> interp_state -> env -> interp_res)
                      : interp_res =
                      match lst with
                      | Literal _ | Pair _ | Struct _ ->
                          Err "Internal Error: loop value has non-list value"
                      | Constructor (_, true, u) -> (* Nil case *)
                          cont (Constructor (listType resTy, true, u)) s env
                      | Constructor (_, false, Pair (hd, tl, _)) -> (* Cons *)
                          let body_env =
                            VariableMap.add elemVar (hd, elemTy) env
                          in interpret body s body_env
                            (* If it continues, we produce no value this
                             * iteration *)
                            (fun s env -> process_foreach tl s env cont)
                            (* If it yields, we'll end up adding that value to
                             * the result of the loop over the tail *)
                            (fun s env (resHd, t) ->
                              if t <> resTy
                              then Err "Yielded incorrect type"
                              else
                                process_foreach tl s env
                                  (fun resTl s env ->
                                    let res =
                                      Constructor (listType resTy,
                                        false, (* cons *)
                                        Pair (resHd, resTl,
                                          Product (resTy, 
                                            Named (listType resTy))))
                                    in cont res s env))
                            ret
                            raise
                      (* TODO: Is it possible to collect the different
                       * behaviors and their results together? That would be
                       * more accurate but probably then make looping over a
                       * ListVal more difficult *)
                      | ListVal (_, elemVal) ->
                          let body_env =
                            VariableMap.add elemVar (elemVal, elemTy) env
                          in interpret body s body_env
                            (* If it continues, we produce an empty list *)
                            (fun s env ->
                              cont 
                                (Constructor (listType resTy, true, valUnit))
                                s env)
                            (* If it yields, we return a new ListVal *)
                            (fun s env (elemRes, t) ->
                              if t <> resTy
                              then Err "Yielded incorrect type"
                              else
                                cont (ListVal (listType resTy, elemRes))
                                  s env)
                            ret
                            raise
                      | _ -> (* Loop over an unknown value *)
                          (* The way we handle loops over unknown lists is to
                           * create some new unknown value to represent all the
                           * items of the list and record the association with
                           * the list value in the state. We then return a
                           * ListVal which indicates a result from an unknown
                           * list *)
                          let (loopvar, uid, s) =
                            match ValueMap.find_opt lst s.loops with
                            | Some (AllUnknown uid) | Some (LastKnown (uid, _))
                                -> (Unknown (Loop uid, elemTy), Some uid, s)
                            | Some (AllKnown v) -> (v, None, s)
                            | None ->
                                let uid = uid ()
                                in let state = {
                                  init = s.init; final = s.final;
                                  loops = ValueMap.add lst (AllUnknown uid) s.loops;
                                  bools = s.bools; constrs = s.constrs }
                                in (Unknown (Loop uid, elemTy), Some uid, state)
                          in let body_env =
                            VariableMap.add elemVar (loopvar, elemTy) env
                          (* This function is used to replace the loop variable
                           * in the resulting state and environment so that all
                           * occurences (other than those in the state on an
                           * element that depends on the loop variable) are
                           * marked as just representing the last element of
                           * the list (i.e., the value that escapes) rather
                           * than an arbitrary element since we are not longer
                           * acting on all elements. *)
                          in let unloop s env : interp_state * env =
                            match uid with
                            | None -> (s, env)
                            | Some uid -> replace_loopvar s env uid
                          in let unloop_val v : value =
                            match uid with
                            | None -> v
                            | Some uid -> replace_loopvar_value v uid
                          in interpret body s body_env
                            (* If it continues, we produce no value *)
                            (fun s env ->
                              let (s, env) = unloop s env
                              in cont 
                                  (Constructor (listType resTy, true, valUnit))
                                  s env)
                            (* If it yields, we construct our ListVal *)
                            (fun s env (res, t) ->
                              let (s, env) = unloop s env
                              in if t <> resTy
                              then Err "Yielded incorrect type"
                              else
                                cont (ListVal (listType resTy, res)) s env)
                            (* For return and raise, we also replace loop vars
                             * in the returned/raised value again since it's
                             * just one value now (though not necessarily the
                             * last... *)
                            (fun s env (v, t) ->
                              let (s, env) = unloop s env
                              in ret s env (unloop_val v, t))
                            (fun s env (v, t) ->
                              let (s, env) = unloop s env
                              in raise s env (unloop_val v, t))
                    in process_foreach v s env
                      (fun res s env ->
                        let new_env =
                          VariableMap.add var
                            (res, Named (listType resTy))
                            env
                        in cont s new_env)
                end
            | _ -> Err "Cannot loop over non list-like type"
        end
    | TryCatch (body, var, catch, finally) ->
        interpret body s env
          (* continue : execute finally and then continue as usual *)
          (fun s env -> interpret finally s env cont yield ret raise)
          (* yield : execute finally and then yield the value, unless the finally did already *)
          (fun s env e ->
            interpret finally s env
              (* continue -- yield e *) (fun s env -> yield s env e)
              (* yield -- just yield *) yield
              (* ret -- just return  *) ret
              (* raise -- just raise *) raise)
          (* ret : execute finally and then return the value, unless the finally did already *)
          (fun s env e ->
            interpret finally s env
              (* continue -- return e *) (fun s env -> ret s env e)
              (* yield -- still ret e *) (fun s env _ -> ret s env e)
              (* ret -- just return   *) ret
              (* raise -- just raise  *) raise)
          (* raise : execute catch and then finally and continue as usual *)
          (fun s env e ->
            interpret catch s (VariableMap.add var e env)
              (* continue -- finally then continue *)
              (fun s env -> interpret finally s env cont yield ret raise)
              (* yield -- finally then yield *)
              (fun s env e ->
                interpret finally s env
                  (* continue - yield e *) (fun s env -> yield s env e)
                  (* yield - just yield *) yield
                  (* ret - just return  *) ret
                  (* raise - just raise *) raise)
              (* ret -- finally then ret *)
              (fun s env e ->
                interpret finally s env
                  (* continue - return e *) (fun s env -> ret s env e)
                  (* yield - still ret e *) (fun s env _ -> ret s env e)
                  (* ret - just return   *) ret
                  (* raise - just raise  *) raise)
              (* raise -- finally then raise *)
              (fun s env e ->
                interpret finally s env
                  (* continue - raise e *) (fun s env -> raise s env e)
                  (* yield - raise e    *) (fun s env _ -> raise s env e)
                  (* ret - just return  *) ret
                  (* raise - just raise *) raise))
    | Localize (el, ex, body) ->
        begin match make_elem_reset el ex s env with
        | Error msg -> Err msg
        | Ok reset_elem ->
            interpret body s env
              (* continue : reset the element and continue *)
              (fun s env -> cont (reset_elem s) env)
              (* yield : reset the element and yield *)
              (fun s env e -> yield (reset_elem s) env e)
              (* ret : reset the element and return *)
              (fun s env e -> ret (reset_elem s) env e)
              (* raise : reset the element and return *)
              (fun s env e -> raise (reset_elem s) env e)
        end
    | Raise e ->
        begin match eval_expr e env with
        | Error msg -> Err msg
        | Ok v -> raise s env v
        end
    | Return e ->
        begin match eval_expr e env with
        | Error msg -> Err msg
        | Ok v -> ret s env v
        end
    | Yield e ->
        begin match eval_expr e env with
        | Error msg -> Err msg
        | Ok v -> yield s env v
        end
end
