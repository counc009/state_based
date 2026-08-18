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

  let empty_state = State { attrs =  AttrMap.empty; elems = ElemMap.empty }

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
