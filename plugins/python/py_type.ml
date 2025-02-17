type py_type_key = int * int * int * int
type py_type_val = string * string list * string

let py_type_tbl : (py_type_key, py_type_val) Hashtbl.t option ref = ref (Some (Hashtbl.create 0))
