open Value

module type STATE = functor (V : VALUE) -> sig
  type t

  val set_attr : t -> V.s -> string -> V.t -> t option
  val pos_elem : t -> V.s -> string -> V.t -> t option
  val neg_elem : t -> V.s -> string -> V.t -> t option

  val get_attr : t -> V.s -> string -> ((t * V.t) -> 'a) -> failure:'a -> 'a
  val check_elem : t -> V.s -> string -> V.t -> (t * bool -> 'a) -> 'a

  (* get_top's continuation takes a (potentially updated) copy of the state and
   * the nested state of the specified top-level element *)
  val get_top : t -> string -> V.t -> (t * t -> 'a) -> failure:'a -> 'a
  val set_top : t -> string -> V.t -> t -> t
end

module ConcreteState : STATE = functor (V : VALUE) -> struct
  module AttrMap = Map.Make(String)

  module ElemMap = Map.Make(struct
    type t = string * V.t
    let compare : t -> t -> int = compare
  end)

  type t = State of { attrs : V.t AttrMap.t; elems : t ElemMap.t }

  let empty_state = State { attrs = AttrMap.empty; elems = ElemMap.empty }

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
          let elems = ElemMap.add (elem, v) empty_state elems
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

  let get_top st elem v (k : t * t -> 'a) ~failure =
    let State { elems; _ } = st
    in match ElemMap.find_opt (elem, v) elems with
    | None -> failure
    | Some res -> k (st, res)

  let set_top st elem v n =
    let State { attrs; elems } = st
    in let elems = ElemMap.add (elem, v) n elems
    in State { attrs; elems }
end

module RandomizeState : STATE = functor (V : VALUE) -> struct
  module AttrMap = Map.Make(String)

  module ElemMap = Map.Make(struct
    type t = string * V.t
    let compare : t -> t -> int = compare
  end)

  type s = State of { attrs : V.t AttrMap.t; elems : (s option) ElemMap.t }
  type t = { attr_gen : V.s -> string -> V.t; init : s; cur : s }

  let empty_s = State { attrs = AttrMap.empty; elems = ElemMap.empty }
  let empty_t attr_gen = { attr_gen; init = empty_s; cur = empty_s }

  let ( let* ) (x : 'a option) (f : 'a -> 'b option) : 'b option = 
    Option.bind x f

  (* This function traverses the state to locate a given location, this
   * potentially involves updating the initial state in places where elements
   * need to exist but were unspecified
   * Returns the state at that location and a function which, given a new state
   * for that location, produces the full updated state *)
  let locate { attr_gen; init; cur } where : (s * (s -> t)) option =
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
      in { attr_gen; init; cur })

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

  let check_elem st where elem v k =
    match locate st where with
    | None -> k (st, false)
    | Some (State { attrs; elems } as st, update) ->
        match ElemMap.find_opt (elem, v) elems with
        | Some None -> k (update st, false)
        | Some (Some _) -> k (update st, true)
        | None ->
            (* TODO: Do we randomize? Or take both? *)
            let choice = true
            in let new_s =
              let new_bind =
                if choice
                then Some empty_s
                else None
              in State { attrs; elems = ElemMap.add (elem, v) new_bind elems }
            in k (update new_s, choice)

  let get_top = failwith "TODO"
  let set_top = failwith "TODO"
end
