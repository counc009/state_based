open Interp

(* FIXME: Actually using state references doesn't help us at all because they
 * can be invalidated by changes to the state. We still need state references
 * to handle nesting but we don't need to change exists and we should add some
 * kind of expression for constructing references.
 * We'll need to update the STATE def to allow us to return some error
 * indicator from everything *)

module ConcreteState : STATE = functor (V : VALUE) -> struct
  module AttrMap = Map.Make(String)

  module ElemMap = Map.Make(struct
    type t = string * V.t
    let compare : t -> t -> int = compare
  end)

  type t = State of { default_absent : bool;
                      attrs : V.t AttrMap.t;
                      elems : t ElemMap.t }

  let empty_state default_absent =
    State { default_absent; attrs =  AttrMap.empty; elems = ElemMap.empty }

  let set_attr st where attr v =
    let rec set (State { default_absent; attrs; elems }) = function
      | V.Here ->
          State { default_absent; attrs = AttrMap.add attr v attrs; elems }
      | V.Nested (elem, v, n) ->
          match ElemMap.find_opt (elem, v) elems with
          | Some st -> set st n
          | None -> failwith "Invalid state reference, missing element"
    in set st where

  let pos_elem st where elem v =
    let rec add (State { default_absent; attrs; elems }) = function
      | V.Here ->
          let elems = ElemMap.add (elem, v) (empty_state default_absent) elems
          in State { default_absent; attrs; elems }
      | V.Nested (elem, v, n) ->
          match ElementMap.find_opt (elem, v) elems with
          | Some st -> add st n
          | None -> failwith "Invalid state reference, missing element"
    in add st where

  let neg_elem st where elem v =
    let rec remove (State { default_absent; attrs; elems }) = function
      | V.Here ->
          let elems = ElemMap.remove (elem, v) elems
          in State { default_absent; attrs; elems }
      | V.Nested (elem, v, n) ->
          match ElementMap.find_opt (elem, v) elems with
          | Some st -> remove st n
          | None -> failwith "Invalid state reference, missing element"
    in remove st where

  let get_attr st where attr (k : t * V.t -> 'a) ~failure =
    let rec find (State { default_absent; attrs; elems }) = function
      | V.Here ->
          begin match AttrMap.find_opt attr attrs with
          | Some v -> k (st, v)
          | None -> failure
          end
      | V.Nested (elem, v, n) ->
          match ElementMap.find
    in find st where
end
