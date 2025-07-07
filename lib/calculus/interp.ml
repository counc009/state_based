let uid = Ast.uid
type uid = Ast.uid

type id = Ast.id

module Interp(Ast : Ast.Ast_Defs) = struct
  open Ast

  module ValueOrder : Map.OrderedType with type t = value = struct
    type t = value
    let compare : value -> value -> int = compare
  end
  module ValueMap : Map.S with type key = value = Map.Make(ValueOrder)

  (* States are made up of maps of qualifiers. For elements, we store the
   * element, value, and whether or not it is negated (true = negated) as the
   * key and the value is qualifiers applied to it. For attributes, the key is
   * just the attribute and whether it is negated and this maps to the value and
   * any qualifiers applied to it. *)
  module ElementOrder : Map.OrderedType with type t = element * value * bool = struct
    type t = element * value * bool
    let compare : t -> t -> int = compare
  end
  module ElementMap : Map.S with type key = element * value * bool
    = Map.Make(ElementOrder)

  module AttributeOrder : Map.OrderedType with type t = attribute = struct
    type t = attribute
    let compare : t -> t -> int = compare
  end
  module AttributeMap : Map.S with type key = attribute
    = Map.Make(AttributeOrder)

  type state = State of state ElementMap.t * (value * state) AttributeMap.t
  let init_state = State (ElementMap.empty, AttributeMap.empty)

  let rec add_qual
      ((q, v, qs) : (element * bool, attribute) Either.t * value * state)
      (State (els, ats) : state) : state =
    match q with
    | Left (elem, neg) ->
        let removed = ElementMap.remove (elem, v, not neg) els
        in let added = ElementMap.update (elem, v, neg)
                        (fun cur ->
                          match cur with
                          | None -> Some qs
                          | Some ps -> Some (add_quals qs ps))
                        removed
        in State (added, ats)
    | Right attr ->
        let added = AttributeMap.update attr
                      (fun cur ->
                        match cur with
                        | None -> Some (v, qs)
                        | Some (_, ps) -> Some (v, add_quals qs ps))
                      ats
        in State (els, added)
  and add_quals (State (els, ats) : state) (ps : state) =
    let rec helper els ats state =
      match els with
      | ((el, v, neg), qs) :: tl
        -> helper tl ats (add_qual (Left (el, neg), v, qs) state)
      | [] ->
          match ats with
          | (at, (v, qs)) :: tl
            -> helper [] tl (add_qual (Right at, v, qs) state)
          | [] -> state
    in helper (ElementMap.bindings els) (AttributeMap.bindings ats) ps

  type loop_info = AllUnknown of uid | AllKnown of value | LastKnown of uid * value

  type prg_type = {
    init : state; final : state;
    loops : loop_info ValueMap.t; (* Map between values and the loop variable over that value *)
    bools : bool ValueMap.t; (* Map between values and its boolean value *)
    constrs : (bool * value) ValueMap.t; (* Map between values and its constructor value (true = L) *)
  }
  let init_prg_type = {
    init = init_state; final = init_state;
    loops = ValueMap.empty;
    bools = ValueMap.empty;
    constrs = ValueMap.empty; }

  (* These functions are used to replace loop variables with just values for
   * handling after the loop ends. This is needed to distinguish actions
   * performed within the loop from uses of the loop variable outside of the
   * loop *)
  let replace_loopvar (s: prg_type) (env: env) (uid: uid) : prg_type * env =
    let rec replaceLoop (v: value) : value =
      match v with
      | Unknown (Loop x, elemTy) when x = uid -> Unknown (Val x, elemTy)
      | Function (f, v, t) -> Function (f, replaceLoop v, t)
      | Pair (x, y, t) -> Pair (replaceLoop x, replaceLoop y, t)
      | Constructor (n, b, v) -> Constructor (n, b, replaceLoop v)
      | Struct (s, r) -> Struct (s, FieldMap.map replaceLoop r)
      | _ -> v
    in let rec containsLoop (v: value) : bool =
      match v with
      | Unknown (Loop x, _) when x = uid -> true
      | Function (_, v, _) -> containsLoop v
      | Pair (x, y, _) -> containsLoop x || containsLoop y
      | Constructor (_, _, v) -> containsLoop v
      | Struct (_, r) -> FieldMap.exists (fun _ v -> containsLoop v) r
      (* ListVal are not checked because they are allowed to contain loop
       * variables (that's basically the whole reason they exist) *)
      | _ -> false
    in let rec helper_els (els : state ElementMap.t) =
      ElementMap.mapi
        (fun (_, v, _) st ->
          if containsLoop v
          then st
          else helper_state st)
        els
    and helper_ats (ats : (value * state) AttributeMap.t) =
      AttributeMap.map (fun (v, st) -> (replaceLoop v, helper_state st)) ats
    and helper_state (State (els, ats) : state) : state =
      State (helper_els els, helper_ats ats)
    in ({ init = helper_state s.init; final = helper_state s.final;
          loops = s.loops; bools = s.bools; constrs = s.constrs; },
        VariableMap.map (fun (v, t) -> (replaceLoop v, t)) env)

  let new_env = VariableMap.empty

  type 'a error = Ok of 'a
                | Err of string
  type prg_res = (prg_type * value) error

  (* A type representing attempting to find some value in a structure where we
   * may or may not find it or may be able to create the value and returns
   * additional information when it is created*)
  type ('a, 'b) find = NotLocated
                     | Located of 'a
                     | Created of 'a * 'b

  (* A list-like type is any named type defined as n = () + t * n
   * Returns the element type is the give type is list like *)
  let list_like (n : namedTy) : typ option =
    let (nil, cons) = namedTyDef n
    in if not (isUnit nil) then None
    else match cons with
         | Product (hd, Named tl) when tl = n -> Some hd
         | _ -> None

  let val_to_type (v : value) : typ =
    match v with
    | Unknown (_, t) -> t
    | Literal (_, p) -> Primitive p
    | Function (_, _, t) -> t
    | Pair (_, _, t) -> t
    | Constructor (n, _, _) -> Named n
    | Struct (s, _) -> Struct s
    | ListVal (n, _) -> Named n

  let substitute_unknown (u: id) (v: value) (s: prg_type) (env: env)
    : (prg_type * env) option =
    (* Substitution here also tries to evaluate expressions further, by seeing
     * whether functions can now reduce *)
    let rec subst_in_value (w: value) : value =
      match w with
      | Unknown (w, _) when u = w -> v
      | Unknown (_, _) | Literal (_, _) -> w
      | Function (f, v, t) ->
          let new_v = subst_in_value v
          in let (_, _, f_def) = funcDef f
          in begin match f_def new_v with
          | Reduced w -> w
          | Stuck -> Function (f, new_v, t)
          | Err msg ->
              (* FIXME *)
              failwith ("While substituting an unknown, a function evaluation failed: " ^ msg)
          end
      | Pair (x, y, t) -> Pair (subst_in_value x, subst_in_value y, t)
      | Constructor (n, c, v) -> Constructor (n, c, subst_in_value v)
      | Struct (t, r) -> Struct (t, FieldMap.map subst_in_value r)
      (* Unlike substituting loop variables where we skip listvals we do handle
       * listvals here since they may contain unknown values that we want to
       * eliminate *)
      | ListVal (n, w) -> ListVal (n, subst_in_value w)
    in let rec subst_in_state (s: state) =
      match s with
      | State (elems, attrs) ->
          let with_elems =
            ElementMap.fold
              (fun (el, v, neg) s new_state ->
                let new_v = subst_in_value v
                in let new_s = subst_in_state s
                in add_qual (Either.Left (el, neg), new_v, new_s) new_state)
              elems
              init_state
          in let with_attrs =
            AttributeMap.fold
              (fun attr (v, s) new_state ->
                let new_v = subst_in_value v
                in let new_s = subst_in_state s
                in add_qual (Either.Right attr, new_v, new_s) new_state)
              attrs
              with_elems
          in with_attrs
    in let new_env = VariableMap.map (fun (v, t) -> (subst_in_value v, t)) env
    in let new_init = subst_in_state s.init
    in let new_final = subst_in_state s.final
    in let new_bools =
      ValueMap.fold
        (fun bound b new_bools ->
          Option.bind new_bools
          (fun new_bools ->
            let new_v = subst_in_value bound
            in match asTruth new_v with
            | Some c -> if b = c then Some new_bools else None
            | None ->
                (* TODO: the substitution (and simplification) might enable us
                 * to simplify the constraint *)
                match ValueMap.find_opt new_v new_bools with
                | None -> Some (ValueMap.add new_v b new_bools)
                | Some c -> if b = c then Some new_bools else None))
        s.bools
        (Some ValueMap.empty)
    in let new_constrs =
      (* The problem with unification is it can produce other substitutions
       * of values that need to be performed. This actually can be implemented
       * and would be nice, but I'm not figuring that all out right now *)
      let unify_values _ _ : (bool * value) ValueMap.t option =
        failwith "unification of values during substitution of an unknown is not supported"
      in ValueMap.fold
        (fun bound (which, arg) new_constrs ->
          Option.bind new_constrs
          (fun new_constrs ->
            let new_v = subst_in_value bound
            in let new_arg = subst_in_value arg
            in match new_v with
            | Constructor (_, c, w) ->
                if which = c then unify_values new_arg w else None
            | _ ->
                match ValueMap.find_opt new_v new_constrs with
                | None ->
                    Some (ValueMap.add new_v (which, new_arg) new_constrs)
                | Some (c, w) ->
                    if which = c then unify_values new_arg w else None))
        s.constrs
        (Some ValueMap.empty)
    in let new_loops =
      let unify_loops _ _ : loop_info ValueMap.t option =
        failwith "unification of loops during substitution of an unknown is not supported"
      in ValueMap.fold
        (fun lst loop new_loops ->
          Option.bind new_loops
          (fun new_loops ->
            let new_lst = subst_in_value lst
            in let new_loop =
              match loop, u with
              | AllUnknown i, Loop j when i = j -> AllKnown v
              | AllUnknown i, Val j when i = j -> LastKnown (i, v)
              | AllUnknown _, _ -> loop
              | AllKnown w, _ -> AllKnown (subst_in_value w)
              | LastKnown (i, _w), Loop j when i = j ->
                  (* FIXME: Should unify w and v *) AllKnown v
              | LastKnown (i, w), _ -> LastKnown (i, subst_in_value w)
            in match ValueMap.find_opt new_lst new_loops with
            | None -> Some (ValueMap.add new_lst new_loop new_loops)
            | Some l -> unify_loops new_loop l))
        s.loops
        (Some ValueMap.empty)
    in Option.bind new_bools (fun new_bools ->
        Option.bind new_constrs (fun new_constrs ->
          Option.bind new_loops (fun new_loops ->
            Some ({ init = new_init; final = new_final;
                    loops = new_loops; bools = new_bools;
                    constrs = new_constrs; }, new_env))))

  let rec addConstraint (v: value) (c: constr) (s: prg_type) (env: env)
    : (prg_type * env) list =
    let addConstraint_basic (v: value) (c : constr) (s: prg_type) (env: env) =
      match c with
      | IsBool b ->
          let new_bools = ValueMap.add v b s.bools
          in ({ init = s.init; final = s.final; loops = s.loops;
                bools = new_bools; constrs = s.constrs; },
              env)
      | IsConstructor (which, (id, typ)) ->
          let new_constrs = ValueMap.add v (which, Unknown (id, typ)) s.constrs
          in ({ init = s.init; final = s.final; loops = s.loops;
                bools = s.bools; constrs = new_constrs; },
              env)
    in let checkValue (v: value) (c: constr) (s: prg_type) (env: env) =
      match c with
      | IsBool b ->
          begin match ValueMap.find_opt v s.bools with
          | Some c when b = c -> Some [(s, env)]
          | Some _ -> Some [] (* b <> c, no way to satisfy this constraint *)
          | None ->
              match asTruth v with
              | Some c when b = c -> Some [(s, env)]
              | Some _ -> Some []
              | None -> None
          end
      | IsConstructor (which, (id, _)) ->
          match ValueMap.find_opt v s.constrs with
          | Some (b, v) when which = b ->
              Option.map (fun x -> [x]) (substitute_unknown id v s env)
          | Some (_, _) -> Some [] (* different constructors, no way to satisfy *)
          | None -> None
    in match checkValue v c s env with
    | Some res -> res
    | None ->
    match v with
    | Unknown (id, typ) ->
        let new_val =
          match c with
          | IsBool b -> boolAsValue b
          | IsConstructor (which, (id, id_typ)) ->
              let ty =
                match typ with
                | Named nm -> nm
                | _ -> failwith "Error: invalid type for constructor"
              in Constructor (ty, which, Unknown (id, id_typ))
        in Option.fold ~none:[] ~some:(fun x -> [x])
            (substitute_unknown id new_val s env)
    | Function (f, arg, _) ->
        begin match reduceFuncConstraint f arg c with
        | Reducible options ->
            List.flatten (List.map
              (fun cs -> List.fold_left
                (fun states c ->
                  match c with
                  | IsBool (v, b) -> List.flatten (List.map
                      (fun (s, env) -> addConstraint v (IsBool b) s env)
                      states)
                  | IsConstructor (v, (which, arg)) -> List.flatten (List.map
                      (fun (s, env) ->
                        addConstraint v (IsConstructor (which, arg)) s env)
                      states)
                  | IsEqual (id, v) ->
                      List.filter_map
                        (fun (s, env) -> substitute_unknown id v s env)
                        states)
                [(s, env)]
                cs)
              options)
        | Unreducible -> [addConstraint_basic v c s env]
        end
    | _ -> [addConstraint_basic v c s env]

  let interpret (s : stmt) (retTy : typ) : prg_res list =
    let rec eval_expr (e : expr) (env : env) : (value * typ) error =
      match e with
      | Function (f, exp) ->
          begin match eval_expr exp env with
          | Err m -> Err m
          | Ok (v, t) ->
              let (argTy, retTy, interp) = funcDef f
              in if t <> argTy
                 then Err "Type error, argument type mismatch"
                 else
                   match interp v with
                   | Reduced w -> Ok (w, retTy)
                   | Stuck -> Ok (Function (f, v, retTy), retTy)
                   | Err msg -> Err msg
          end
      | Literal l ->
          let p = literalTyp l
          in Ok (Literal (l, p), Primitive p)
      | Variable v ->
          begin match VariableMap.find_opt v env with
          | None -> Err "Undefined variable"
          | Some v -> Ok v
          end
      | Pair (x, y) ->
          begin match eval_expr x env, eval_expr y env with
          | Ok (x, tx), Ok (y, ty)
            -> let t : typ = Product (tx, ty) in Ok (Pair (x, y, t), t)
          | Err m, Err n -> Err (m ^ "\n" ^ n)
          | Err m, Ok _ -> Err m
          | Ok _ , Err n -> Err n
          end
      | Env -> Ok (envToVal env, envType)
    (* Returns either the element or the attribute, the value, and attached qualifiers *)
    in let rec eval_qual (q : qual) (env : env)
      : ((element * bool, attribute) Either.t * value * state) error =
      match q with
      | Attribute (_, e, qs) | Element (_, e, qs) ->
          let bq = match q with Attribute (at, _, _) -> Either.Right at
                              | Element   (el, _, _) -> Either.Left (el, false)
                              | _ -> failwith "Match error"
          in begin match eval_expr e env with
          | Err msg -> Err msg
          | Ok (v, _) ->
              match eval_quals qs env with
              | Err msg -> Err msg
              | Ok state -> Ok (bq, v, state)
          end
      | NotElement (el, e) ->
          match eval_expr e env with
          | Err msg -> Err msg
          | Ok (v, _) -> Ok (Left (el, true), v, init_state)
    and eval_quals (qs : qual list) (env : env) : state error =
      match qs with
      | [] -> Ok init_state
      | q :: qs ->
          match eval_qual q env with
          | Err msg -> Err msg
          | Ok qres ->
              match eval_quals qs env with
              | Err msg -> Err msg
              | Ok state -> Ok (add_qual qres state)
    (* Given an attribute AST and the current state, finds the attribute either
     * in the final state or initial state, and (if necessary) adds the
     * desired attribute with an unknown value.
     * Returns the value of the attribute and resulting state *)
    in let get_attribute (a : attr) (s : prg_type) (env : env) : (value * prg_type) error =
      (* The helper traverses an attribute and a state to find the attribute's
       * value (and returns the modified state if needed). Can fail by error or
       * can return Ok NotLocated if it could not find some qualifier needed on
       * the desired path *)
      let rec helper (a : attr) (State (els, ats)) : (value, state) find error =
        match a with
        | AttrAccess a ->
            begin match AttributeMap.find_opt a ats with
            | Some (v, _) -> Ok (Located v)
            | None ->
                let v : value = Unknown (Val (uid ()), attributeDef a)
                in Ok (Created (v, State (els, AttributeMap.add a (v, init_state) ats)))
            end
        | OnAttribute (a, at) ->
            begin match AttributeMap.find_opt a ats with
            | None ->
                (* Even if the attribute doens't exist, we could create it
                 * (since it's an attribute), so we do that and see what
                 * happens *)
                begin match helper at init_state with
                | Err msg -> Err msg
                | Ok NotLocated -> Ok NotLocated
                | Ok (Located _) -> failwith "Cannot find attribute in empty state"
                | Ok (Created (v, st)) ->
                    let new_value : value = Unknown (Val (uid ()), attributeDef a)
                    in let new_ats = AttributeMap.add a (new_value, st) ats
                    in Ok (Created (v, State (els, new_ats)))
                end
            | Some (av, qs) ->
                match helper at qs with
                | Err msg -> Err msg
                | Ok NotLocated -> Ok NotLocated
                | Ok (Located v) -> Ok (Located v)
                | Ok (Created (v, st)) ->
                    let new_ats = AttributeMap.add a (av, st) ats
                    in Ok (Created (v, State (els, new_ats)))
            end
        | OnElement (el, e, at) ->
            begin match eval_expr e env with
            | Err msg -> Err msg
            | Ok (v, _) ->
                match ElementMap.find_opt (el, v, false) els with
                | None -> Ok NotLocated
                | Some qs ->
                    match helper at qs with
                    | Err msg -> Err msg
                    | Ok NotLocated -> Ok NotLocated
                    | Ok (Located v) -> Ok (Located v)
                    | Ok (Created (res, st)) ->
                        let new_els = ElementMap.add (el, v, false) st els
                        in Ok (Created (res, State (new_els, ats)))
            end
      in match helper a s.final with
         | Err msg -> Err msg
         | Ok (Located v) -> Ok (v, s)
         | Ok (Created (v, new_final)) ->
             (* We prefer to create a value for an attribute on the initial
              * state rather than the final state since that way if we set one
              * attribute and then fetch another we still put that value onto
              * the original state rather than creating it on the final state *)
             begin match helper a s.init with
             | Ok (Located v) -> Ok (v, s)
             | Ok (Created (v, new_init)) ->
                 Ok (v, { init = new_init; final = s.final; loops = s.loops;
                          bools = s.bools; constrs = s.constrs; })
             | _ -> Ok (v, { init = s.init; final = new_final; loops = s.loops;
                             bools = s.bools; constrs = s.constrs; })
             end
         | Ok NotLocated ->
             match helper a s.init with
             | Err msg -> Err msg
             | Ok NotLocated -> Err "Failed to locate attribute in current state"
             | Ok (Located v) -> Ok (v, s)
             | Ok (Created (v, new_init)) ->
                 Ok (v, { init = new_init; final = s.final; loops = s.loops;
                          bools = s.bools; constrs = s.constrs; })
    (* Either returns whether or not the element is in the state (left) or
     * new initial states assuming the element does and does not exist
     * respectively (right) *)
    in let has_element (e : elem) (s : prg_type) (env : env)
      : (bool, state * state) Either.t error =
      (* Returns whether the given element only has attributes except at the
       * last level, returns an error if there's an error in evaluating the
       * expression on that last level *)
      let rec only_attrs (el : elem) : bool error =
        match el with
        | Element (_, e) | NotElement (_, e) ->
            begin match eval_expr e env with
            | Err msg -> Err msg
            | Ok _ -> Ok true
            end
        | OnElement _ -> Ok false
        | OnAttribute (_, el) -> only_attrs el
      in let rec helper (el : elem) (State (els, ats)) : bool option error =
        match el with
        | Element _ | NotElement _ ->
            let (elm, e, neg)
              = match el with Element (elm, e)    -> (elm, e, false)
                            | NotElement (elm, e) -> (elm, e, true)
                            | _ -> failwith "Match Failure"
            in begin match eval_expr e env with
            | Err msg -> Err msg
            | Ok (v, _) ->
                match ElementMap.find_opt (elm, v, neg) els with
                | Some _ -> Ok (Some true)
                | None ->
                    match ElementMap.find_opt (elm, v, not neg) els with
                    | Some _ -> Ok (Some false)
                    | None -> Ok None
            end
        | OnAttribute (at, q) ->
            begin match AttributeMap.find_opt at ats with
            | None ->
                (* If this attribute doesn't exist but the element being checked
                 * for is on the end of a series of attributes (with no
                 * elements), we could create all the attributes and then create
                 * the positive/negative of the attribute.
                 * Otherwise, if there's an element then we are unable to locate
                 * the desired qualifier *)
                begin match only_attrs q with
                | Err msg -> Err msg
                | Ok true -> Ok None
                | Ok false -> Err "Failed to locate element in state"
                end
            | Some (_, st) -> helper q st
            end
        | OnElement (el, e, q) ->
            begin match eval_expr e env with
            | Err msg -> Err msg
            | Ok (v, _) ->
                match ElementMap.find_opt (el, v, false) els with
                | None -> Err "Failed to locate element in state"
                | Some st -> helper q st
            end
      in let rec add_elem (el : elem) (State (els, ats)) : state * state =
        match el with
        | Element _ | NotElement _ ->
            let (elem, e, neg)
              = match el with Element (elm, e)    -> (elm, e, false)
                            | NotElement (elm, e) -> (elm, e, true)
                            | _ -> failwith "Match Failure"
            in begin match eval_expr e env with
            | Err _ -> failwith "Error evaluating expression"
            | Ok (v, _) ->
                let new_true = ElementMap.add (elem, v, neg) init_state els
                in let new_false = ElementMap.add (elem, v, not neg) init_state els
                in (State (new_true, ats), State (new_false, ats))
            end
        | OnAttribute (at, el) ->
            begin match AttributeMap.find_opt at ats with
            | None ->
                let v : value = Unknown (Val (uid ()), attributeDef at)
                in let (new_true, new_false) = add_elem el init_state
                in let ats_true = AttributeMap.add at (v, new_true) ats
                in let ats_false = AttributeMap.add at (v, new_false) ats
                in (State (els, ats_true), State (els, ats_false))
            | Some (v, st) ->
                let (new_true, new_false) = add_elem el st
                in let ats_true = AttributeMap.add at (v, new_true) ats
                in let ats_false = AttributeMap.add at (v, new_false) ats
                in (State (els, ats_true), State (els, ats_false))
            end
        | OnElement (el, e, q) ->
            begin match eval_expr e env with
            | Err _ -> failwith "Error evaluating expression"
            | Ok (v, _) ->
                let st = ElementMap.find (el, v, false) els
                in let (new_true, new_false) = add_elem q st
                in let els_true = ElementMap.add (el, v, false) new_true els
                in let els_false = ElementMap.add (el, v, false) new_false els
                in (State (els_true, ats), State (els_false, ats))
            end
      in match helper e s.final with
      | Err msg -> Err msg
      | Ok (Some b) -> Ok (Left b)
      | Ok None ->
          match helper e s.init with
          | Err msg -> Err msg
          | Ok (Some b) -> Ok (Left b)
          | Ok None -> Ok (Right (add_elem e s.init))
    (* Notes on loops: the bodies must return a pair of the value yielded by
     * each iteration and the the special expression "Env", which is used to
     * thread the environment back to the processing here so so that loop can
     * modify the environment outside of it. This does mean you cannot return a
     * value for an entire action from inside a loop *)
    in let rec process_foreach (lst: value) (elemTy: typ) (var: variable)
                        (resTy: typ) (body: stmt)  (s: prg_type) (env: env)
                        : ((value * typ) * prg_type * env) error list =
      match lst with
      | Literal _ | Pair _ | Struct _ ->
          failwith "Loop value has non-list value"
      | Constructor (_, true, u) -> (* Nil case *)
          [Ok ((Constructor (listType resTy, true, u), Named (listType resTy)),
                s, env)]
      | Constructor (_, false, Pair (hd, tl, _)) -> (* Cons case *)
          let res_hd = interp body s (VariableMap.add var (hd, elemTy) env)
                              (Product (resTy, envType))
          in List.flatten
            (List.map
              (fun s ->
                match s with Err msg -> [Err msg]
                | Ok (s, Pair (resHd, envv, _)) ->
                    let res_tl = process_foreach tl elemTy var resTy body s
                                                 (envFromVal envv)
                    in List.map (fun resTl ->
                      match resTl with Err msg -> Err msg
                      | Ok ((resTl, resTy), resS, resEnv) ->
                        Ok ((Constructor (listType resTy, false,
                            Pair (resHd, resTl,
                              Product (resTy, Named (listType resTy)))),
                            Named (listType resTy)),
                         resS, resEnv))
                      res_tl
                | _ -> failwith "Return from for-each body must be a pair")
              res_hd)
      | ListVal (_, elemVal) ->
          let res = interp body s (VariableMap.add var (elemVal, elemTy) env)
                           (Product (resTy, envType))
          in List.map
            (fun s -> match s with Err msg -> Err msg
              | Ok (s, Pair (res, envv, _)) ->
                  Ok ((ListVal (listType resTy, res), Named (listType resTy)),
                      s, envFromVal envv)
              | _ -> failwith "Return from for-each body must be a pair")
            res
      | _ -> (* Loop over an unknown value *)
          (* The way we handle loops over unknown lists is to assign the value
           * we loop over a particular UID which represents the loop variable
           * while we loop over that list. We record this information in the
           * state so we can reconstruct repeat constructs at the end, without
           * having to deal with them during interpretation *)
          (* Identify whether there's already a "loop variable" for looping over
           * this value. If so, use it, otherwise create our own.
           * If we create our own, we also update the map in the state *)
          (* The result of looping over an unknown value will be a ListVal *)
          let (loopvar, uid, s) =
            match ValueMap.find_opt lst s.loops with
            | Some (AllUnknown uid) | Some (LastKnown (uid, _))
                -> (Unknown (Loop uid, elemTy), Some uid, s)
            | Some (AllKnown v) -> (v, None, s)
            | None ->
                let uid = uid ()
                in let state = { init  = s.init; final = s.final;
                                 loops = ValueMap.add lst (AllUnknown uid) s.loops;
                                 bools = s.bools; constrs = s.constrs; }
                in (Unknown (Loop uid, elemTy), Some uid, state)
          in let res_loop
            = interp body s (VariableMap.add var (loopvar, elemTy) env)
                     (Product (resTy, envType))
          in List.map
              (fun s -> match s with Err msg -> Err msg
                (* Note that we replace the loop variable in the state and
                 * environment. What this does is replaces all occurences of
                 * it in the environment and any instance in the state that
                 * is not contained within an element depending on the
                 * loop variable. This ensures that if the value is accessed
                 * from outside the loop we can distinguish that it was not
                 * the result of a loop, rather it takes the value of the
                 * last element of the list.
                 * We don't do this to the value in the resulting ListVal since
                 * that is allowed to preserve these loop variables *)
                | Ok (s, Pair (res, envv, _)) ->
                    let (state, env) =
                      Option.fold ~none:(s, env)
                        ~some:(fun uid -> replace_loopvar s (envFromVal envv) uid)
                        uid
                    in Ok ((ListVal (listType resTy, res), Named (listType resTy)),
                           state, env)
                | _ -> failwith "Return from for-each body must be a pair")
              res_loop
    and interp (b : stmt) (s : prg_type) (env : env) (ret : typ) : prg_res list =
      match b with
      | Action   (var, action, expr, next) ->
          let (arg, in_type, out_type, body) = actionDef action
          in begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              if t <> in_type
              then Err "Incorrect argument type to action" :: []
              else let results = interp body s (VariableMap.singleton arg (v, t)) out_type
              in List.flatten
                  (List.map (fun r ->
                      match r with
                      | Ok (s, v) ->
                          interp next s (VariableMap.add var (v, out_type) env) ret
                      | Err msg -> Err msg :: []) results)
          end
      | Assign   (var, expr, next) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              interp next s (VariableMap.add var (v, t) env) ret
          end
      | Add      (qual, next) ->
          begin match eval_qual qual env with
          | Err msg -> Err msg :: []
          | Ok q ->
              (* Note: Add does not even look at the initial environment,
               * technically we could check it and not add this if it's a
               * duplicate, but that's generally unlikely to be useful and
               * could be cleaned up after the fact if we want.
               *)
              let new_final = add_qual q s.final
              in let new_state = { init = s.init; final = new_final;
                                   loops = s.loops; bools = s.bools;
                                   constrs = s.constrs; }
              in interp next new_state env ret
          end
      | Get      (var, attr, next) ->
          begin match get_attribute attr s env with
          | Err msg -> Err msg :: []
          | Ok (v, new_state) ->
              interp next new_state (VariableMap.add var (v, val_to_type v) env) ret
          end
      (* Contains only needs to handle the addition of one constraint where the
         last level is just an element. Adding attributes is handled by get
         and constraining the values on elements should be handled by
         constraints produced by Cond and Match *)
      | Contains (elem, thn, els) ->
          begin match has_element elem s env with
          | Err msg -> Err msg :: []
          (* If we definitively have or do not have the constraint, take the
           * appropriate branch *)
          | Ok (Left b) ->
              interp (if b then thn else els) s env ret
          (* Otherwise, take both branches in appropriate updated initial states *)
          | Ok (Right (new_init_true, new_init_false)) ->
              (interp thn { init = new_init_true; final = s.final;
                            loops = s.loops; bools = s.bools; constrs = s.constrs; }
                      env ret)
              @
              (interp els { init = new_init_false; final = s.final;
                            loops = s.loops; bools = s.bools; constrs = s.constrs; }
                      env ret)
          end
      (* For both cond and match we try to reduce the expression to a concrete
       * value that we can branch on. However, if it cannot reduce to such an
       * expression then we try both possible options (which involves
       * interacting with the constraints of the current state) *)
      | Cond     (expr, thn, els) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              if not (isTruthType t)
              then Err "Condition is not truthy" :: []
              else match asTruth v with
                   | Some true -> interp thn s env ret
                   | Some false -> interp els s env ret
                   (* Since the value cannot be evaluated fully try both
                    * possible values *)
                   | None ->
                      (List.flatten
                        (List.map
                          (fun (s, env) -> interp thn s env ret)
                          (addConstraint v (IsBool true) s env)))
                      @
                      (List.flatten
                        (List.map
                          (fun (s, env) -> interp els s env ret)
                          (addConstraint v (IsBool false) s env)))
          end
      | Match    (expr, var, left, right) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              match t with
              | Named n ->
                  begin match v with
                  | Constructor (_, b, v) ->
                      let t = (if b then fst else snd) (namedTyDef n)
                      in interp (if b then left else right) s
                            (VariableMap.add var (v, t) env) ret
                  (* The value cannot be evaluated sufficiently, so try both
                   * options *)
                  | _ ->
                      let type_left = fst (namedTyDef n)
                      in let id_left : id = Val (uid ())
                      in let val_left = Unknown (id_left, type_left)
                      in let type_right = snd (namedTyDef n)
                      in let id_right : id = Val (uid ())
                      in let val_right = Unknown (id_right, type_right)
                      in let env_left =
                        VariableMap.add var (val_left, type_left) env
                      in let env_right =
                        VariableMap.add var (val_right, type_right) env
                      in (List.flatten
                        (List.map
                          (fun (s, env) -> interp left s env ret)
                          (addConstraint v (IsConstructor (true, (id_left, type_left)))
                            s env_left)))
                      @ (List.flatten
                        (List.map
                          (fun (s, env) -> interp right s env ret)
                          (addConstraint v (IsConstructor (false, (id_right, type_right)))
                            s env_right)))
                  end
              | _ -> Err "Cannot match over non-named type" :: []
          end
      | ForEach (var, resTyp, lst, elemVar, body, next) ->
          begin match eval_expr lst env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              match t with
              | Named n ->
                  begin match list_like n with
                  | None -> Err "Cannot loop over non list-like type" :: []
                  | Some elemTy ->
                      let results
                        = process_foreach v elemTy elemVar resTyp body s env
                      in List.flatten
                        (List.map
                          (fun res ->
                            match res with Err msg -> [Err msg]
                            | Ok (res, s, env) ->
                              let new_env = VariableMap.add var res env
                              in interp next s new_env ret)
                          results)
                  end
              | _ -> Err "Cannot loop over non-list-like type" :: []
          end
      | Fail     msg -> (Err msg) :: []
      | Return   expr ->
          begin match eval_expr expr env with
          | Ok (v, t) ->
              if t <> ret
              then Err "Incorrect return type" :: []
              else Ok (s, v) :: []
          | Err msg -> Err msg :: []
          end
    in interp s init_prg_type new_env retTy
end
