type t

val zero : t
val one : t

val ( + ) : t -> t -> t
val ( - ) : t -> t -> t
val ( * ) : t -> t -> t
val ( / ) : t -> t -> t

val add : t -> t -> t
val sub : t -> t -> t
val mul : t -> t -> t
val div : t -> t -> t
val abs : t -> t
val neg : t -> t

val of_float : float -> t
val to_float : t -> float

val compare : t -> t -> int
