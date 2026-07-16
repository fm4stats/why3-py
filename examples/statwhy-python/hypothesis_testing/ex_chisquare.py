# translated from the first part of examples/mlw/ex_chisquare.mlw

from statwhy import real
from statwhy import Unspecified, dataset, array
from statwhy import Nil, Cons, Param, CategoricalD
from statwhy import exec_chisquare_test

#@ use cameleerBHL.CameleerBHL
#@ use chisquare.Chisquare
#@ use list.Length
#@ use array.Array

p1 = Param("p1")
p2 = Param("p2")
p3 = Param("p3")
p4 = Param("p4")

p = CategoricalD(Cons(p1, Cons(p2, Cons(p3, Cons(p4, Nil)))))

def ex_chisquare4(d : dataset[int], q : array[real]) -> real :
    #@ requires \
    #@    d.scale = Unspecified /\ \
    #@    is_empty !st /\ \
    #@    sampled d p /\ \
    #@    Length.length d.data = length q = 4 /\ \
    #@    for_all (fun i -> i >= 5) d.data /\ \
    #@    let size = from_int (sum d.data) in \
    #@    (q[0] *. size >=. 5.0) /\ \
    #@    (q[1] *. size >=. 5.0) /\ \
    #@    (q[2] *. size >=. 5.0) /\ \
    #@    (q[3] *. size >=. 5.0) /\ \
    #@    is_prob_dist (Cons p1 (Cons p2 (Cons p3 (Cons p4 Nil)))) (World !st interp) /\ \
    #@    is_prob_dist_const (Cons q[0] (Cons q[1] (Cons q[2] (Cons q[3] Nil)))) /\ \
    #@    ((World !st interp) |= Possible (param_term p1 $< const_term q[0])) /\ \
    #@    ((World !st interp) |= Possible (param_term p1 $> const_term q[0])) /\ \
    #@    ((World !st interp) |= Possible (param_term p2 $< const_term q[1])) /\ \
    #@    ((World !st interp) |= Possible (param_term p2 $> const_term q[1])) /\ \
    #@    ((World !st interp) |= Possible (param_term p3 $< const_term q[2])) /\ \
    #@    ((World !st interp) |= Possible (param_term p3 $> const_term q[2])) /\ \
    #@    ((World !st interp) |= Possible (param_term p4 $< const_term q[3])) /\ \
    #@    ((World !st interp) |= Possible (param_term p4 $> const_term q[3]))

    #@ ensures \
    #@    let h = ((param_term p1) $!= (const_term q[0])) $|| \
    #@            ((param_term p2) $!= (const_term q[1])) $|| \
    #@            ((param_term p3) $!= (const_term q[2])) $|| \
    #@            ((param_term p4) $!= (const_term q[3])) in \
    #@    let p = result in \
    #@    Eq p = compose_pvs h !st && \
    #@    (World !st interp) |= StatB (Eq p) h
    return exec_chisquare_test(p, Cons(q[0], Cons(q[1], Cons(q[2], Cons(q[3], Nil)))), d)

#@ execution

d = dataset(data=[10,25,30,30], scale=Unspecified)
q = [0.10, 0.25, 0.35, 0.30]

print("p-value: %f" % ex_chisquare4(d, q))
