open Value

module type STATE = sig
  type t
  type vt
  type vs

  val set_attr : t -> vs -> string -> vt -> t option
  val pos_elem : t -> vs -> string -> vt -> t option
  val neg_elem : t -> vs -> string -> vt -> t option

  val get_attr : t -> vs -> string -> ((t * vt) -> 'a) -> failure:'a -> 'a
  val check_elem : t -> vs -> string -> vt -> (t * bool -> 'a) -> 'a

  val localize : t -> string -> vt -> (t -> 'a) -> failure:'a
    -> update:('a -> (t -> t) -> 'a) -> 'a

  type setup
  val empty_state : setup -> t

  val string_of_state : t -> string
end

module ConcreteState (V : VALUE) 
  : STATE with type vt = V.t and type vs = V.s and type setup = unit
= struct
  type vt = V.t
  type vs = V.s

  module AttrMap = Map.Make(String)
  module ElemMap = Map.Make(struct
    type t = string * V.t
    let compare : t -> t -> int = compare
  end)

  type t = State of { attrs : V.t AttrMap.t; elems : t ElemMap.t }

  let empty_t = State { attrs = AttrMap.empty; elems = ElemMap.empty }

  type setup = unit
  let empty_state () = empty_t

  let ( let* ) (x : 'a option) (f : 'a -> 'b option) : 'b option = 
    Option.bind x f

  let set_attr st where attr v =
    let rec set (State { attrs; elems }) = function
      | V.Here ->
          let attrs = AttrMap.add attr v attrs
          in Some (State { attrs; elems })
      | V.Nested (elem, v, n) ->
          let* st = ElemMap.find_opt (elem, v) elems
          in set st n
    in set st where

  let pos_elem st where elem v =
    let rec add (State { attrs; elems }) = function
      | V.Here ->
          let elems = ElemMap.add (elem, v) empty_t elems
          in Some (State { attrs; elems })
      | V.Nested (elem, v, n) ->
          let* st = ElemMap.find_opt (elem, v) elems
          in add st n
    in add st where

  let neg_elem st where elem v =
    let rec remove (State { attrs; elems }) = function
      | V.Here ->
          let elems = ElemMap.remove (elem, v) elems
          in Some (State { attrs; elems })
      | V.Nested (elem, v, n) ->
          let* st = ElemMap.find_opt (elem, v) elems
          in remove st n
    in remove st where

  let get_attr st where attr (k : t * V.t -> 'a) ~failure =
    let rec find (State { attrs; elems }) = function
      | V.Here ->
          begin match AttrMap.find_opt attr attrs with
          | None -> failure
          | Some v -> k (st, v)
          end
      | V.Nested (elem, v, n) ->
          begin match ElemMap.find_opt (elem, v) elems with
          | None -> failure
          | Some st -> find st n
          end
    in find st where

  let check_elem st where elem v (k : t * bool -> 'a) =
    let rec check (State { attrs; elems }) = function
      | V.Here ->
          if ElemMap.mem (elem, v) elems
          then k (st, true)
          else k (st, false)
      | V.Nested (elem, v, n) ->
          begin match ElemMap.find_opt (elem, v) elems with
          | None -> k (st, false)
          | Some st -> check st n
          end
    in check st where

  let localize st elem v (k : t -> 'a) ~failure ~update =
    let State { attrs; elems } = st
    in match ElemMap.find_opt (elem, v) elems with
    | None -> failure
    | Some local_s ->
        let update_state (State { attrs; elems }) =
          let elems = ElemMap.add (elem, v) local_s elems
          in State { attrs; elems }
        in update (k st) update_state

  let string_of_state st : string =
    let rec convert (indent : string) (State { attrs; elems }) =
      let string_of_attr attr v = indent ^ attr ^ " = " ^ V.string_of_value v
      in let attr_lines =
        AttrMap.fold (fun attr v res -> string_of_attr attr v :: res) attrs []
      in let string_of_elem (elem, v) n = 
        indent ^ elem ^ "(" ^ V.string_of_value v ^ ")" ^ "\n"
        ^ convert ("  " ^ indent) n
      in let lines =
        ElemMap.fold (fun elem n res -> string_of_elem elem n :: res) elems
          attr_lines
      in String.concat "\n" lines
    in convert "  " st
end

(* This is called a Randomized State because the original idea was that we
 * randomize the state as we discover it, so if we check whether an element
 * is present or absent and we're not sure yet we consult a (possibly random)
 * function to decide. However, it can also be used to model an actual system,
 * we can take the information we're asked about and check the appropriate
 * result to respond with. *)
module RandomizeState (V : VALUE)
: STATE with type vt = V.t and type vs = V.s
    and type setup = (V.s -> string -> V.t) * (V.s -> string -> V.t -> bool)
= struct
  type vt = V.t
  type vs = V.s

  module AttrMap = Map.Make(String)

  module ElemMap = Map.Make(struct
    type t = string * V.t
    let compare : t -> t -> int = compare
  end)

  type s = State of { attrs : V.t AttrMap.t; elems : (s option) ElemMap.t }
  type t = { attr_gen : V.s -> string -> V.t;
             elem_pick : V.s -> string -> V.t -> bool;
             init : s; cur : s }

  let empty_s = State { attrs = AttrMap.empty; elems = ElemMap.empty }
  let empty_t attr_gen elem_pick =
    { attr_gen; elem_pick; init = empty_s; cur = empty_s }

  type setup = (V.s -> string -> V.t) * (V.s -> string -> V.t -> bool)
  let empty_state (attr_gen, elem_pick) = empty_t attr_gen elem_pick

  let ( let* ) (x : 'a option) (f : 'a -> 'b option) : 'b option = 
    Option.bind x f

  (* This function traverses the state to locate a given location, this
   * potentially involves updating the initial state in places where elements
   * need to exist but were unspecified
   * Returns the state at that location and a function which, given a new state
   * for that location, produces the full updated state *)
  let locate { attr_gen; elem_pick; init; cur } where : (s * (s -> t)) option =
    (* Returns the state we located and a function which given an update to
     * the current state, returns an updated initial state (if we had to add to
     * it to locate the desired state) and an updated current state *)
    let rec locate (init : s option) (cur : s)
    : V.s -> (s * (s -> s option * s)) option
    = function
      | V.Here -> Some (cur, fun new_s -> (None, new_s))
      | V.Nested (elem, v, n) ->
          let State { attrs = cur_attrs; elems = cur_elems } = cur
          in begin match ElemMap.find_opt (elem, v) cur_elems with
          (* Element DOES NOT exist in the current state, cannot locate it *)
          | Some None -> None
          (* Element DOES exist in the current state, proceed after we figure
           * out whether or not it exists in the initial state *)
          | Some (Some cur) ->
              let cur_update = fun new_s ->
                State {
                  attrs = cur_attrs;
                  elems = ElemMap.add (elem, v) (Some new_s) cur_elems
                }
              in let (init_rec, init_update) =
                match init with
                | None ->
                    (None, 
                     function
                       | Some _ -> failwith "Internal Error: locate should not create init state when none provided"
                       | None -> None)
                | Some (State { attrs = init_attrs; elems = init_elems }) ->
                    begin match ElemMap.find_opt (elem, v) init_elems with
                    | Some None ->
                        (None,
                        function
                          | Some _ -> failwith "Internal Error: locate should not create init state when none provided"
                          | None -> None)
                    | Some (Some init) ->
                        (Some init,
                        function
                          | None -> None
                          | Some new_bind ->
                              Some (State {
                                attrs = init_attrs;
                                elems = ElemMap.add (elem, v) (Some new_bind) init_elems
                              }))
                    | None ->
                        (Some empty_s,
                        function
                          | None -> None
                          | Some new_bind ->
                              Some (State {
                                attrs = init_attrs;
                                elems = ElemMap.add (elem, v) (Some new_bind) init_elems
                              }))
                    end
              in let* (res, update) = locate init_rec cur n
              in Some (res, fun new_s ->
                let (inner_init, inner_cur) = update new_s
                in let init_res = init_update inner_init
                in let cur_res = cur_update inner_cur
                in (init_res, cur_res))
          (* Element may or may not exist, try adding it to the initial and
           * current states *)
          | None ->
              begin match init with
              (* If we don't have an initial state, we can't add an element *)
              | None -> None
              | Some (State { attrs = init_attrs; elems = init_elems }) ->
                  let* (res, update) = locate (Some empty_s) empty_s n
                  in Some (res, fun new_s ->
                    let (init_update, cur_update) = update new_s
                    in let init_res =
                      let new_binding =
                        match init_update with
                        | None -> empty_s
                        | Some s -> s
                      in Some (State {
                        attrs = init_attrs;
                        elems =
                          ElemMap.add (elem, v) (Some new_binding) init_elems
                      })
                    in let cur_res =
                      State {
                        attrs = cur_attrs;
                        elems =
                          ElemMap.add (elem, v) (Some cur_update) cur_elems }
                    in (init_res, cur_res))
              end
          end
    in let* (res, update) = locate (Some init) cur where
    in Some (res, fun new_s ->
      let (init_update, cur) = update new_s
      in let init =
        match init_update with
        | None -> init
        | Some init -> init
      in { attr_gen; elem_pick; init; cur })

  let set_attr st where attr v =
    let* (State { attrs; elems }, k) = locate st where
    in let attrs = AttrMap.add attr v attrs
    in Some (k (State { attrs; elems }))

  let pos_elem st where elem v =
    let* (State { attrs; elems }, k) = locate st where
    in let elems = ElemMap.add (elem, v) (Some empty_s) elems
    in Some (k (State { attrs; elems }))

  let neg_elem st where elem v =
    let* (State { attrs; elems }, k) = locate st where
    in let elems = ElemMap.add (elem, v) None elems
    in Some (k (State { attrs; elems }))

  let get_attr st where attr k ~failure =
    let attr_gen = st.attr_gen
    in match locate st where with
    | None -> failure
    | Some (State { attrs; elems } as st, update) ->
        match AttrMap.find_opt attr attrs with
        | None ->
            let v = attr_gen where attr
            in let new_s =
              State { attrs = AttrMap.add attr v attrs; elems }
            in k (update new_s, v)
        | Some v -> k (update st, v)

  let ( let> ) (x : ('a -> 'b) -> 'c) (f : 'a -> 'b) : 'c = x f

  (* check_elem uses its own locating function because the locate function we
   * use everywhere else will create all intermediate elements which were
   * unknown because those functions are either for add (which adds these
   * intermediate elements) or to get an attribute in which case if there are
   * missing intermediate elements we would have a failure and it is always
   * better to avoid a failure if we can.
   * But for check_elem if there is an unknown intermediate element we can
   * either create it as positive or negative and either way is valid *)
  let check_elem st where elem v k =
    let elem_pick = st.elem_pick
    in let rec check (init : s option) (cur : s) where
      (k : s option * s * bool -> 'a) =
      let State { attrs = cur_attrs; elems = cur_elems } = cur
      in match where with
      | V.Here ->
          begin match ElemMap.find_opt (elem, v) cur_elems with
          | Some None -> k (None, cur, false)
          | Some (Some _) -> k (None, cur, true)
          | None ->
              match init with
              | None -> k (None, cur, false)
              | Some (State { attrs = init_attrs; elems = init_elems }) ->
                  let choice = elem_pick where elem v
                  in let init =
                    let bind = if choice then Some empty_s else None
                    in State { attrs = init_attrs;
                               elems = ElemMap.add (elem, v) bind init_elems }
                  in let cur =
                    let bind = if choice then Some empty_s else None
                    in State { attrs = cur_attrs;
                               elems = ElemMap.add (elem, v) bind cur_elems }
                  in k (Some init, cur, choice)
          end
      | V.Nested (elem, v, n) ->
          begin match ElemMap.find_opt (elem, v) cur_elems with
          | Some None -> k (None, cur, false)
          | Some (Some cur_rec) ->
              let init_rec =
                match init with
                | None -> None
                | Some (State { elems; _ }) ->
                    match ElemMap.find_opt (elem, v) elems with
                    | None -> None
                    | Some i -> i
              in let> (n_init, n_cur, cond) = check init_rec cur_rec n
              in let init =
                match n_init with
                | None -> None
                | Some bind ->
                    match init with
                    | None -> failwith "check_elem should never create an initial state when not provided one"
                    | Some (State { attrs; elems }) ->
                        Some (State { attrs;
                          elems = ElemMap.add (elem, v) (Some bind) elems })
              in let cur =
                State { attrs = cur_attrs;
                        elems = ElemMap.add (elem, v) (Some n_cur) cur_elems }
              in k (init, cur, cond)
          | None ->
              match init with
              | None -> k (None, cur, false)
              | Some (State { attrs = init_attrs; elems = init_elems }) ->
                  let choice = elem_pick where elem v
                  in if not choice
                  then
                    let init =
                      State { attrs = init_attrs;
                              elems = ElemMap.add (elem, v) None init_elems }
                    in let cur =
                      State { attrs = cur_attrs;
                              elems = ElemMap.add (elem, v) None cur_elems }
                    in k (Some init, cur, false)
                  else
                    let> (n_init, n_cur, cond) = check (Some empty_s) empty_s n
                    in let init =
                      let binding = Option.value ~default:empty_s n_init
                      in State {
                        attrs = init_attrs;
                        elems = ElemMap.add (elem, v) (Some binding) init_elems
                      }
                    in let cur =
                      State {
                        attrs = cur_attrs;
                        elems = ElemMap.add (elem, v) (Some n_cur) cur_elems
                      }
                    in k (Some init, cur, cond)
          end
    in let { attr_gen; elem_pick; init; cur } = st
    in let> (init_update, cur, cond) = check (Some init) cur where
    in let init = Option.value ~default:init init_update
    in let st = { attr_gen; elem_pick; init; cur }
    in k (st, cond)

  let rec merge_states (State { attrs = init_attrs; elems = init_elems })
                       (State { attrs = cur_attrs;  elems = cur_elems }) =
    let attrs =
      AttrMap.merge (fun _ init_val cur_val ->
        match init_val, cur_val with
        | _, Some v | Some v, None -> Some v
        | None, None -> None
      ) init_attrs cur_attrs
    in let elems =
      ElemMap.merge (fun _ init_st cur_st ->
        match init_st, cur_st with
        | None, None -> None
        | None, Some st | Some None, Some st | Some st, None -> Some st
        | _, Some None -> Some None
        | Some (Some init_st), Some (Some cur_st) ->
            Some (Some (merge_states init_st cur_st))
      ) init_elems cur_elems
    in State { attrs; elems }

  let localize st elem v (k : t -> 'a) ~failure ~update =
    let { attr_gen; elem_pick;
          init = State { attrs = init_attrs; elems = init_elems };
          cur = State { attrs = cur_attrs; elems = cur_elems } } = st
    in match ElemMap.find_opt (elem, v) cur_elems with
    | Some None -> failure
    | Some (Some local_st) ->
        let update_state
          { attr_gen; elem_pick;
            init = State { attrs = init_attrs; elems = init_elems } as init;
            cur = State { attrs = cur_attrs; elems = cur_elems } } =
          let init_st =
            match ElemMap.find_opt (elem, v) init_elems with
            | None -> empty_s
            | Some None -> empty_s
            | Some (Some init_st) -> init_st
          in let res_st = merge_states init_st local_st
          in let cur_elems = ElemMap.add (elem, v) (Some res_st) cur_elems
          in { attr_gen; elem_pick; init; 
               cur = State { attrs = cur_attrs; elems = cur_elems } }
        in update (k st) update_state
    | None ->
        let st = { attr_gen; elem_pick;
                   init = State {
                      attrs = init_attrs;
                      elems = ElemMap.add (elem, v) (Some empty_s) init_elems
                   };
                   cur = State {
                     attrs = cur_attrs;
                     elems = ElemMap.add (elem, v) (Some empty_s) cur_elems } }
        in let update_state
          { attr_gen; elem_pick;
            init = State { attrs = init_attrs; elems = init_elems } as init;
            cur = State { attrs = cur_attrs; elems = cur_elems } } =
          let init_st =
            match ElemMap.find_opt (elem, v) init_elems with
            | None -> empty_s
            | Some None -> empty_s
            | Some (Some init_st) -> init_st
          in let cur_elems = ElemMap.add (elem, v) (Some init_st) cur_elems
          in { attr_gen; elem_pick; init; 
               cur = State { attrs = cur_attrs; elems = cur_elems } }
        in update (k st) update_state

  let string_of_state { cur = st; _ } : string =
    let rec convert (indent : string) (State { attrs; elems }) =
      let string_of_attr attr v = indent ^ attr ^ " = " ^ V.string_of_value v
      in let attr_lines =
        AttrMap.fold (fun attr v res -> string_of_attr attr v :: res) attrs []
      in let string_of_elem (elem, v) n = 
        match n with
        | None -> indent ^ "NOT " ^ elem ^ "(" ^ V.string_of_value v ^ ")"
        | Some n ->
            indent ^ elem ^ "(" ^ V.string_of_value v ^ ")" ^ "\n"
            ^ convert ("  " ^ indent) n
      in let lines =
        ElemMap.fold (fun elem n res -> string_of_elem elem n :: res) elems
          attr_lines
      in String.concat "\n" lines
    in convert "  " st
end
