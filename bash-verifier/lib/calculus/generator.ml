(* A generator can be paired with a RandomimzedState to explore a space of
 * states; rather than just randomly generating responses they track the
 * responses they have given and will lead us through exploring the entire
 * space (using some randomness so that we sample the space if we're not
 * sampling it fully. *)
open Value
open State

type ternary = Present | Absent | Either

module Generator (V : VALUE) : sig
  class generator : (V.s -> string -> V.t list)
  -> (V.s -> string -> V.t -> ternary) 
  -> (V.s -> string -> V.t list list)
  -> object
    method init : unit
    method reset : bool
    method gen_attr : V.s -> string -> V.t
    method pick_elem : V.s -> string -> V.t -> bool
    method gen_elems : V.s -> string -> V.t list
  end
end = struct
  (* We track the space to explore as a tree of unexplored nodes and nodes we've
   * explored for which we track how many of its children are nonempty (i.e.,
   * there are more options left in the space) and those options *)
  type 'v traverse_space =
    | Unexplored
    | Node of {
        mutable nonempty : int;
        mutable selected : int;
        (* select maps [0, nonempty) to the index of a non-empty option *)
        mutable select   : int array;
                options  : 'v iarray;
                children : 'v traverse_space ref iarray }

  type gen_info = Bool of bool | Value of V.t | Elems of V.t list

  class generator 
    (attr_gen  : V.s -> string -> V.t list)
    (elem_pick : V.s -> string -> V.t -> ternary)
    (elems_gen : V.s -> string -> V.t list list)
  = object (self)
    val root = ref Unexplored
    val mutable cur  = ref Unexplored

    method init = cur <- root

    method reset =
      let () = cur <- root
      in let rec update = function
        | Unexplored -> false
        | Node ({ nonempty; selected; select; options; children } as n) ->
            let selected_more = update !(Iarray.get children selected)
            in if selected_more
            then true
            else
              let () =
                Array.blit select (selected + 1) 
                           select selected
                           (Array.length select - 1 - selected)
              in let () = n.nonempty <- nonempty - 1
              in nonempty > 1
      in update !root

    method gen_attr (where : V.s) (attr : string) =
      let () =
        match !cur with
        | Unexplored ->
            let options     = List.map (fun v -> Value v) (attr_gen where attr)
            in let options  = Iarray.of_list options
            in let nonempty = Iarray.length options
            in let children = Iarray.init nonempty (fun _ -> ref Unexplored)
            in let select   = Array.init nonempty (fun x -> x)
            in let () =
              cur := Node { nonempty; select; selected = 0; options; children }
            in ()
        | Node _ -> ()
      in match !cur with
      | Unexplored -> failwith "match error"
      | Node ({ nonempty; select; options; children; _ } as n) ->
          let j = Random.int nonempty
          in let i = select.(j)
          in let () = n.selected <- i
          in let () = cur <- Iarray.get children i
          in let res =
            match Iarray.get options i with
            | Bool _  ->
                failwith "Asked to generate an attribute but found a bool"
            | Value v -> v
            | Elems _ ->
                failwith "Asked to generate an attribute but found elements"
          in res

    method pick_elem (where : V.s) (elem : string) (v : V.t) =
      let () =
        match !cur with
        | Unexplored ->
            let options =
              match elem_pick where elem v with
              | Present -> [Bool true]
              | Absent  -> [Bool false]
              | Either -> [Bool true; Bool false]
            in let options  = Iarray.of_list options
            in let nonempty = Iarray.length options
            in let children = Iarray.init nonempty (fun _ -> ref Unexplored)
            in let select   = Array.init nonempty (fun x -> x)
            in let () =
              cur := Node { nonempty; select; selected = 0; options; children }
            in ()
        | Node _ -> ()
      in match !cur with
      | Unexplored -> failwith "match error"
      | Node ({ nonempty; select; options; children; _ } as n) ->
          let j = Random.int nonempty
          in let i = select.(j)
          in let () = n.selected <- i
          in let () = cur <- Iarray.get children i
          in let res =
            match Iarray.get options i with
            | Bool b -> b
            | Value _ -> failwith "Asked to generate a bool but found a value"
            | Elems _ ->
                failwith "Asked to generate an attribute but found elements"
          in res

    method gen_elems (where : V.s) (elem : string) =
      let () =
        match !cur with
        | Unexplored ->
            let options     = List.map (fun vs -> Elems vs) (elems_gen where elem)
            in let options  = Iarray.of_list options
            in let nonempty = Iarray.length options
            in let children = Iarray.init nonempty (fun _ -> ref Unexplored)
            in let select   = Array.init nonempty (fun x -> x)
            in let () =
              cur := Node { nonempty; select; selected = 0; options; children }
            in ()
        | Node _ -> ()
      in match !cur with
      | Unexplored -> failwith "match error"
      | Node ({ nonempty; select; options; children; _ } as n) ->
          let j = Random.int nonempty
          in let i = select.(j)
          in let () = n.selected <- i
          in let () = cur <- Iarray.get children i
          in let res =
            match Iarray.get options i with
            | Bool _ -> failwith "Asked to generate elems but found a bool"
            | Value _ -> failwith "Asked to generate elems but found a value"
            | Elems vs -> vs
          in res
  end
end
