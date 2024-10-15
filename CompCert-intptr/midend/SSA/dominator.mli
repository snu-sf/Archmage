 
val dominator : (int -> int list) -> (int -> int list) -> int -> int -> 
  int array * (int -> bool) * int array

val make_children : int array -> int -> int list
