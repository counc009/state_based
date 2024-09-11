type uid = Ast.uid

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

  module AttributeOrder : Map.OrderedType with type t = attribute * bool = struct
    type t = attribute * bool
    let compare : t -> t -> int = compare
  end
  module AttributeMap : Map.S with type key = attribute * bool
    = Map.Make(AttributeOrder)

  type state = State of state ElementMap.t * (value * state) AttributeMap.t
  let init_state = State (ElementMap.empty, AttributeMap.empty)

  let rec add_qual
      ((q, v, qs, neg) : (element, attribute) Either.t * value * state * bool)
      (State (els, ats) : state) : state =
    match q with
    | Left elem ->
        let removed = ElementMap.remove (elem, v, not neg) els
        in let added = ElementMap.update (elem, v, neg)
                        (fun cur ->
                          match cur with
                          | None -> Some qs
                          | Some ps -> Some (add_quals qs ps))
                        removed
        in State (added, ats)
    | Right attr ->
        let removed = AttributeMap.remove (attr, not neg) ats
        in let added = AttributeMap.update (attr, neg)
                        (fun cur ->
                          match cur with
                          | None -> Some (v, qs)
                          | Some (_, ps) -> Some (v, add_quals qs ps))
                        removed
        in State (els, added)
  and add_quals (State (els, ats) : state) (ps : state) =
    let rec helper els ats state =
      match els with
      | ((el, v, neg), qs) :: tl
        -> helper tl ats (add_qual (Left el, v, qs, neg) state)
      | [] ->
          match ats with
          | ((at, neg), (v, qs)) :: tl
            -> helper [] tl (add_qual (Right at, v, qs, neg) state)
          | [] -> state
    in helper (ElementMap.bindings els) (AttributeMap.bindings ats) ps

  type prg_type = { init : state; final : state; loops : uid ValueMap.t; }
  let init_prg_type = { init = init_state; final = init_state; loops = ValueMap.empty; }

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
    (* Returns either the element or the attribute, the value, attached qualifiers,
     * and whether it is negated (true) or not (false) *)
    in let rec eval_qual (q : qual) (env : env)
      : ((element, attribute) Either.t * value * state * bool) error =
      match q with
      | BaseQual (bq, qs) ->
          begin match eval_bqual bq env with
          | Err msg -> Err msg
          | Ok (q, v) ->
              match eval_quals qs env with
              | Err msg -> Err msg
              | Ok state -> Ok (q, v, state, false)
          end
      | NotQual bq ->
          match eval_bqual bq env with
          | Err msg -> Err msg
          | Ok (q, v) -> Ok (q, v, init_state, true)
    and eval_bqual (q : bqual) (env : env) : ((element, attribute) Either.t * value) error =
      let (qbase, e) = match q with Attribute (at, e) -> (Either.Right at, e)
                                  | Element   (el, e) -> (Either.Left  el, e)
      in match eval_expr e env with
      | Err msg -> Err msg
      | Ok (v, _) -> Ok (qbase, v)
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
            begin match AttributeMap.find_opt (a, false) ats with
            | Some (v, _) -> Ok (Located v)
            | None ->
                let v : value = Unknown (ref (), attributeDef a)
                in Ok (Created (v, State (els, AttributeMap.add (a, false) (v, init_state) ats)))
            end
        | OnAttribute (a, at) ->
            begin match AttributeMap.find_opt (a, false) ats with
            | None -> Ok NotLocated
            | Some (av, qs) ->
                match helper at qs with
                | Err msg -> Err msg
                | Ok NotLocated -> Ok NotLocated
                | Ok (Located v) -> Ok (Located v)
                | Ok (Created (v, st)) ->
                    let new_ats = AttributeMap.add (a, false) (av, st) ats
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
                    | Ok (Created (v, st)) ->
                        let new_els = ElementMap.add (el, v, false) st els
                        in Ok (Created (v, State (new_els, ats)))
            end
      in match helper a s.final with
         | Err msg -> Err msg
         | Ok (Located v) -> Ok (v, s)
         | Ok (Created (v, new_final)) ->
             (* If we can create a value for the attribute in the final state,
              * we return that unless we can find a value for the attribute
              * in the initial state *)
             begin match helper a s.init with
             | Ok (Located v) -> Ok (v, s)
             | _ -> Ok (v, { init = s.init; final = new_final; loops = s.loops; })
             end
         | Ok NotLocated ->
             match helper a s.init with
             | Err msg -> Err msg
             | Ok NotLocated -> Err "Failed to locate attribute in current state"
             | Ok (Located v) -> Ok (v, s)
             | Ok (Created (v, new_init)) ->
                 Ok (v, { init = new_init; final = s.final; loops = s.loops; })
    (* Notes on loops: the bodies should return the special expression "Env",
     * which is used to thread the environment back to the processing here so
     * so that loop can modify the environment outside of it. This does mean
     * you cannot return a value for an entire action from inside a loop *)
    (* Note: ret arg here is the return for the next statement not the loop *)
    in let rec process_loop (var : variable) (lst : value) (elemTy : typ)
                            (body : stmt) (next : stmt) (s : prg_type)
                            (env : env) (ret : typ) : prg_res list =
      match lst with
      | Literal _ | Pair _ | Struct _ ->
          failwith "Loop value has non-list value"
      | Constructor (_, true, _) -> (* Nil case *)
          interp next s env ret
      | Constructor (_, false, Pair (hd, tl, _)) -> (* Cons case *)
          let res_hd = interp body s (VariableMap.add var (hd, elemTy) env) envType
          in List.flatten
              (List.map
                (fun s ->
                  match s with Err msg -> [Err msg]
                  | Ok (s, e) ->
                      process_loop var tl elemTy body next s (envFromVal e) ret)
                res_hd)
      | _ -> (* Loop over an unknown value *)
          (* The way we handle loops over unknown lists is to assign the value
           * we loop over a particular UID which represents the loop variable
           * while we loop over that list. We record this information in the
           * state so we can reconstruct repeat constructs at the end, without
           * having to deal with them during interpretation *)
          (* Identify whether there's already a "loop variable" for looping over
           * this value. If so, use it, otherwise create our own.
           * If we create our own, we also update the map in the state *)
          let (uid, s) =
            match ValueMap.find_opt lst s.loops with
            | Some uid -> (uid, s)
            | None ->
                let uid = ref ()
                in let state = { init  = s.init; final = s.final;
                                 loops = ValueMap.add lst uid s.loops; }
                in (uid, state)
          in let head : value = Unknown (uid, elemTy)
          in let res_loop = interp body s (VariableMap.add var (head, elemTy) env) envType
          in List.flatten
              (List.map
                (fun s ->
                  match s with Err msg -> [Err msg]
                  | Ok (s, e) -> interp next s (envFromVal e) ret)
                res_loop)
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
               *
               * FIXME
               * This could have weird interactions with get, since it checks
               * the final state first and so if we have [user(u) file(foo)] in the
               * final state and [content(c) file(foo)] in the initial,
               * get would create a new unknown for the content even though
               * we know the contents.
               *
               * FIX: In get, track whether we created a new unknown and if we
               * did in the final state check the initial state for an existing
               * value
               *)
              let new_final = add_qual q s.final
              in let new_state = { init = s.init; final = new_final; loops = s.loops }
              in interp next new_state env ret
          end
      | Get      (var, attr, next) ->
          begin match get_attribute attr s env with
          | Err msg -> Err msg :: []
          | Ok (v, new_state) ->
              interp next new_state (VariableMap.add var (v, val_to_type v) env) ret
          end
      | Contains (qual, thn, els) -> [] (* TODO *)
      (* TODO: For both cond and match, if the result of expression is not
       * a concrete value we could evaluate both branches and track the
       * "constraint" of what we've assumed the value was (this is much like
       * you would do with refinement/dependent types). For the moment I have
       * not done this for simplicity
       *)
      | Cond     (expr, thn, els) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              if not (isTruthType t)
              then Err "Condition is not truthy" :: []
              else match asTruth v with
                   (* If we were to track the constraints, we would do that here *)
                   | None -> Err "Could not evaluate truth of condition" :: []
                   | Some true -> interp thn s env ret
                   | Some false -> interp els s env ret
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
                  (* Modify here to track constraints *)
                  | _ -> Err "Could not evaluate to constructor on match" :: []
                  end
              | _ -> Err "Cannot match over non-named type" :: []
          end
      | Loop     (var, expr, body, next) ->
          begin match eval_expr expr env with
          | Err msg -> Err msg :: []
          | Ok (v, t) ->
              match t with
              | Named n ->
                  begin match list_like n with
                  | None -> Err "Cannot loop over non list-like type" :: []
                  | Some elemTy ->
                      process_loop var v elemTy body next s env ret
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
