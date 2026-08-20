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

  val each_elem : t -> vs -> string -> ('a -> vt -> 'a) -> (t -> 'a) -> 'a

  val localize : t -> string -> vt -> (t -> 'a) -> failure:'a
    -> update:('a -> (t -> t) -> 'a) -> 'a

  type setup
  val empty_state : setup -> t

  type attr_ex
  type elem_ex
  val extract_attributes : t -> (string * attr_ex) list
  val extract_elements   : t -> ((string * vt) * elem_ex) list
end

module rec ConcreteState : functor (V : VALUE) -> STATE
  with type vt      = V.t
   and type vs      = V.s
   and type setup   = unit
   and type attr_ex = V.t
   and type elem_ex = ConcreteState(V).t
= functor (V : VALUE) -> struct
  type vt = V.t
  type vs = V.s
  
  module AttrMap = Map.Make(String)
  module ElemMap : sig
    type key = string * V.t
    type !+'a t

    val empty : 'a t

    val add : key -> 'a -> 'a t -> 'a t
    val add_if_absent : key -> 'a -> 'a t -> 'a t
    val remove : key -> 'a t -> 'a t

    val find_opt : key -> 'a t -> 'a option
    val mem : key -> 'a t -> bool

    val to_list : 'a t -> (key * 'a) list
    val list_of_elem : string -> 'a t -> V.t list
  end = struct
    module StringMap = Map.Make(String)
    module ValueMap = Map.Make(struct
      type t = V.t
      let compare : t -> t -> int = compare
    end)

    type key = string * V.t
    type !+'a t = ('a ValueMap.t) StringMap.t

    let empty = StringMap.empty

    let add (elem, v) x m =
      StringMap.update elem
        (function
          | None -> Some (ValueMap.singleton v x)
          | Some m -> Some (ValueMap.add v x m))
        m

    let add_if_absent (elem, v) x m =
      StringMap.update elem
        (function
          | None -> Some (ValueMap.singleton v x)
          | Some m -> Some (ValueMap.update v
            (function
              | None -> Some x
              | Some x -> Some x)
            m)
        ) m

    let remove (elem, v) m =
      StringMap.update elem
        (function
          | None -> None
          | Some m -> Some (ValueMap.remove v m))
        m

    let find_opt (elem, v) m =
      match StringMap.find_opt elem m with
      | None -> None
      | Some m -> ValueMap.find_opt v m

    let mem (elem, v) m =
      match StringMap.find_opt elem m with
      | None -> false
      | Some m -> ValueMap.mem v m

    let to_list m =
      StringMap.fold (fun elem n res ->
        ValueMap.fold (fun v b res -> ((elem, v), b) :: res) n res)
        m []

    let list_of_elem elem m =
      match StringMap.find_opt elem m with
      | None -> []
      | Some m -> List.map fst (ValueMap.bindings m)
  end

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
          let elems = ElemMap.add_if_absent (elem, v) empty_t elems
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

  let each_elem st where elem (iter : 'a -> V.t -> 'a) (init : t -> 'a) : 'a =
    let rec each (State { attrs; elems }) = function
      | V.Here ->
          List.fold_left iter (init st) (ElemMap.list_of_elem elem elems)
      | V.Nested (elem, v, n) ->
          begin match ElemMap.find_opt (elem, v) elems with
          | None -> init st
          | Some st -> each st n
          end
    in each st where

  let localize st elem v (k : t -> 'a) ~failure ~update =
    let State { attrs; elems } = st
    in match ElemMap.find_opt (elem, v) elems with
    | None -> failure
    | Some local_s ->
        let update_state (State { attrs; elems }) =
          let elems = ElemMap.add (elem, v) local_s elems
          in State { attrs; elems }
        in update (k st) update_state

  (* Extraction of a Concrete State just returns the values of attributes and
   * the nested states of elements *)
  type attr_ex = V.t
  type elem_ex = t

  let extract_attributes (State { attrs; _ }) = AttrMap.to_list attrs
  let extract_elements   (State { elems; _ }) = ElemMap.to_list elems
end

type presence = Unknown | Absent | Present

(* This is called a Randomized State because the original idea was that we
 * randomize the state as we discover it, so if we check whether an element
 * is present or absent and we're not sure yet we consult a (possibly random)
 * function to decide. However, it can also be used to model an actual system,
 * we can take the information we're asked about and check the appropriate
 * result to respond with. *)
module rec RandomizeState : functor (V : VALUE) -> STATE 
  with type vt = V.t
   and type vs = V.s
   and type setup = (V.s -> string -> V.t) * (V.s -> string -> V.t -> bool)
   and type attr_ex = V.t option * V.t option
   and type elem_ex = presence * presence * RandomizeState(V).t option
= functor (V : VALUE) -> struct
  type vt = V.t
  type vs = V.s

  module AttrMap = Map.Make(String)
  module ElemMap : sig
    type key = string * V.t
    type !+'a t

    val empty : 'a t

    val add : key -> 'a -> 'a t -> 'a t
    val add_if_absent : key -> 'a -> 'a t -> 'a t
    val remove : key -> 'a t -> 'a t

    val find_opt : key -> 'a t -> 'a option option

    val is_elem_known : string -> 'a t -> bool
    val make_elem_known : string -> 'a t -> 'a t
    (* Make all elements known (even absent elements) *)
    val make_known : 'a t -> 'a t

    val to_list : 'a t -> (key * 'a option) list
    val list_of_elem : string -> 'a t -> V.t list

    val merge : 
      (key -> 'a option option -> 'b option option -> 'c option option)
      -> 'a t -> 'b t -> 'c t
    val fold : (key -> 'a option -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc
  end = struct
    module StringMap = Map.Make(String)
    module ValueMap = Map.Make(struct
      type t = V.t
      let compare : t -> t -> int = compare
    end)

    type key = string * V.t
    (* The bools are true to indicate that missing values indicate absence and
     * false to indicate that missing values represent unknown state.
     * It always starts as unknown but when we do a each_elem it will become
     * missing and if an element was absent and we add it we also mark its
     * nested state as missing *)
    type !+'a t = bool * (bool * 'a option ValueMap.t) StringMap.t

    let empty = (false, StringMap.empty)

    let add (elem, v) x (b, m) =
      (b, StringMap.update elem
        (function
          | None -> Some (b, ValueMap.singleton v (Some x))
          | Some (b, m) -> Some (b, ValueMap.add v (Some x) m))
        m)

    let add_if_absent (elem, v) x (b, m) =
      (b, StringMap.update elem
        (function
          | None -> Some (b, ValueMap.singleton v (Some x))
          | Some (b, m) -> Some (b, ValueMap.update v
            (function
              | None -> Some (Some x)
              | Some x -> Some x)
            m)
        ) m)

    let remove (elem, v) (b, m) =
      (b, StringMap.update elem
        (function
          | None -> Some (b, ValueMap.singleton v None)
          | Some (b, m) -> Some (b, ValueMap.add v None m))
        m)

    let find_opt (elem, v) (known, m) =
      match StringMap.find_opt elem m with
      | None -> if known then Some None else None
      | Some (known, m) ->
          match ValueMap.find_opt v m with
          | None -> if known then Some None else None
          | Some r -> Some r

    let is_elem_known elem (known, m) =
      match StringMap.find_opt elem m with
      | None -> known
      | Some (known, _) -> known

    let make_elem_known elem (b, m) =
      (b, StringMap.update elem
        (function
          | None -> Some (true, ValueMap.empty)
          | Some (_, m) -> Some (true, m)
        ) m)

    let make_known (_, m) = (true, m)

    let to_list (_, m) =
      StringMap.fold (fun elem (_, n) res ->
        ValueMap.fold (fun v b res -> ((elem, v), b) :: res) n res)
        m []

    let list_of_elem elem (known, m) =
      match StringMap.find_opt elem m with
      | None when known -> []
      | None | Some (false, _) ->
          failwith "list_of_elem should only be called on a known element"
      | Some (true, m) ->
          List.filter_map (fun (v, b) ->
            match b with
            | None -> None
            | Some _ -> Some v
          ) (ValueMap.bindings m)

    let merge f (b, n) (c, m) =
      (b || c, StringMap.merge (fun elem n m ->
        match n, m with
        | None, None -> None
        | Some (b, n), None ->
            Some (b, 
              ValueMap.filter_map (fun v n -> f (elem, v) (Some n) None) n)
        | None, Some (c, m) ->
            Some (c,
              ValueMap.filter_map (fun v m -> f (elem, v) None (Some m)) m)
        | Some (b, n), Some (c, m) ->
            Some (b || c,
              ValueMap.merge (fun v n m -> f (elem, v) n m) n m)) n m)

    let fold f (_, m) acc =
      StringMap.fold (fun elem (_, m) acc ->
        ValueMap.fold (fun v m acc -> f (elem, v) m acc) m acc
      ) m acc
  end

  type s = State of { attrs : V.t AttrMap.t; elems : s ElemMap.t }
  type t = { attr_gen : V.s -> string -> V.t;
             elem_pick : V.s -> string -> V.t -> bool;
             init : s; cur : s }

  let empty_s = State { attrs = AttrMap.empty; elems = ElemMap.empty }
  let empty_s_known = State { 
    attrs = AttrMap.empty;
    elems = ElemMap.make_known ElemMap.empty }

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
                  elems = ElemMap.add (elem, v) new_s cur_elems
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
                                elems = ElemMap.add (elem, v) new_bind init_elems
                              }))
                    | None ->
                        (Some empty_s,
                        function
                          | None -> None
                          | Some new_bind ->
                              Some (State {
                                attrs = init_attrs;
                                elems = ElemMap.add (elem, v) new_bind init_elems
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
                          ElemMap.add (elem, v) new_binding init_elems
                      })
                    in let cur_res =
                      State {
                        attrs = cur_attrs;
                        elems =
                          ElemMap.add (elem, v) cur_update cur_elems }
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
    in let elems =
      match ElemMap.find_opt (elem, v) elems with
      (* If the element's state is unknown it may already exist and have stuff
       * nested on it, so we do not set it to known *)
      | None -> ElemMap.add (elem, v) empty_s elems
      (* But if it doesn't already exist, then we can set it to fully known *)
      | Some None ->
          ElemMap.add (elem, v) empty_s_known elems
      (* If it already exists, we don't update it *)
      | Some (Some _) -> elems
    in Some (k (State { attrs; elems }))

  let neg_elem st where elem v =
    let* (State { attrs; elems }, k) = locate st where
    in let elems = ElemMap.remove (elem, v) elems
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

  let rec ref_diff full part =
    if full = part
    then V.Here
    else
      match full with
      | V.Here -> V.Here
      | V.Nested (elem, v, n) -> V.Nested (elem, v, ref_diff n part)

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
                    let elems =
                      if choice
                      then ElemMap.add (elem, v) empty_s init_elems
                      else ElemMap.remove (elem, v) init_elems
                    in State { attrs = init_attrs; elems }
                  in let cur =
                    let elems =
                      if choice
                      then ElemMap.add (elem, v) empty_s cur_elems
                      else ElemMap.remove (elem, v) cur_elems
                    in State { attrs = cur_attrs; elems }
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
                    | None -> Some empty_s
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
                          elems = ElemMap.add (elem, v) bind elems })
              in let cur =
                State { attrs = cur_attrs;
                        elems = ElemMap.add (elem, v) n_cur cur_elems }
              in k (init, cur, cond)
          | None ->
              match init with
              | None -> failwith "Current state should not be unknown when initial state is absent"
              | Some (State { attrs = init_attrs; elems = init_elems }) ->
                  let choice = elem_pick (ref_diff where n) elem v
                  in if not choice
                  then
                    let init =
                      State { attrs = init_attrs;
                              elems = ElemMap.remove (elem, v) init_elems }
                    in let cur =
                      State { attrs = cur_attrs;
                              elems = ElemMap.remove (elem, v) cur_elems }
                    in k (Some init, cur, false)
                  else
                    let> (n_init, n_cur, cond) = check (Some empty_s) empty_s n
                    in let init =
                      let binding = Option.value ~default:empty_s n_init
                      in State {
                        attrs = init_attrs;
                        elems = ElemMap.add (elem, v) binding init_elems
                      }
                    in let cur =
                      State {
                        attrs = cur_attrs;
                        elems = ElemMap.add (elem, v) n_cur cur_elems
                      }
                    in k (Some init, cur, cond)
          end
    in let { attr_gen; elem_pick; init; cur } = st
    in let> (init_update, cur, cond) = check (Some init) cur where
    in let init = Option.value ~default:init init_update
    in let st = { attr_gen; elem_pick; init; cur }
    in k (st, cond)

  (* TODO *)
  let each_elem st where elem (iter : 'a -> V.t -> 'a) (init : t -> 'a) : 'a =
    init st

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
          in let cur_elems = ElemMap.add (elem, v) res_st cur_elems
          in { attr_gen; elem_pick; init; 
               cur = State { attrs = cur_attrs; elems = cur_elems } }
        in update (k st) update_state
    | None ->
        let st = { attr_gen; elem_pick;
                   init = State {
                      attrs = init_attrs;
                      elems = ElemMap.add (elem, v) empty_s init_elems
                   };
                   cur = State {
                     attrs = cur_attrs;
                     elems = ElemMap.add (elem, v) empty_s cur_elems } }
        in let update_state
          { attr_gen; elem_pick;
            init = State { attrs = init_attrs; elems = init_elems } as init;
            cur = State { attrs = cur_attrs; elems = cur_elems } } =
          let init_st =
            match ElemMap.find_opt (elem, v) init_elems with
            | None -> empty_s
            | Some None -> empty_s
            | Some (Some init_st) -> init_st
          in let cur_elems = ElemMap.add (elem, v) init_st cur_elems
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

  (* Extraction of a Randomized State returns the values and nested states of
   * both the initial and current state *)
  type attr_ex = V.t option * V.t option
  type elem_ex = presence * presence * t option

  let extract_attributes
    { init = State { attrs = init_attrs; _ };
      cur = State  { attrs = cur_attrs;  _ }; _ } =
    AttrMap.to_list 
      (AttrMap.merge (fun _ i c -> Some (i, c)) init_attrs cur_attrs)
  (* TODO: We need some way to indicate when a set of elements is fully known
   * (i.e., there cannot be others) *)
  let extract_elements
    { init = State { elems = init_elems; _ };
      cur = State  { elems = cur_elems;  _ }; attr_gen; elem_pick } =
    let merge_bindings i c : (presence * presence * t option) option =
      let extract_state x =
        match x with
        | None          -> (Unknown, empty_s)
        | Some None     -> (Absent, empty_s)
        | Some (Some s) -> (Present, s)
      in let (i, init) = extract_state i
      in let (c, cur)  = extract_state c
      in match i, c with
      | Unknown, Unknown -> None
      | Absent, Unknown | Unknown, Absent | Absent, Absent ->
          Some (i, c, None)
      | _, _ -> Some (i, c, Some { attr_gen; elem_pick; init; cur })

    in let keys = ElemMap.merge (fun _ _ _ -> Some None) init_elems cur_elems
    in ElemMap.fold (fun el _ acc ->
      let i = ElemMap.find_opt el init_elems
      in let c = ElemMap.find_opt el cur_elems
      in match merge_bindings i c with
      | None -> acc
      | Some x -> (el, x) :: acc
    ) keys []
end
