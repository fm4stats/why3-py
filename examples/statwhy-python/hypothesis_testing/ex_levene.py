# translated from the first part of examples/mlw/ex_levene.mlw.

from statwhy import Nil, Cons, string, UnknownD, real, Two, dataset, Interval
from statwhy import exec_levene
#@ use cameleerBHL.CameleerBHL
#@ use levene.Levene

p1 = UnknownD("p1")
p2 = UnknownD("p2")
p3 = UnknownD("p3")

def ex_levene3(d1, d2, d3) -> real:
    #@ requires \
    #@    is_empty !st /\ \
    #@    sampled d1 p1 /\ sampled d2 p2 /\ sampled d3 p3 /\ \
    #@    independent_list (Cons d1 (Cons d2 (Cons d3 Nil))) /\ \
    #@    d1.scale = d2.scale = d3.scale = Interval /\ \
    #@    (World !st interp) |= Possible (var p1 $< var p2) /\ \
    #@    (World !st interp) |= Possible (var p1 $< var p3) /\ \
    #@    (World !st interp) |= Possible (var p2 $< var p3) /\ \
    #@    (World !st interp) |= Possible (var p1 $> var p2) /\ \
    #@    (World !st interp) |= Possible (var p1 $> var p3) /\ \
    #@    (World !st interp) |= Possible (var p2 $> var p3)
    #@ ensures \
    #@    let p = result in \
    #@    let h = (var p1 $!= var p2) $|| (var p1 $!= var p3) $|| (var p2 $!= var p3) in \
    #@    Eq p = compose_pvs h !st && \
    #@    (World !st interp) |= StatB (Eq p) h
    return exec_levene(Cons(p1, Cons(p2, Cons(p3, Nil))), \
                       Cons(d1, Cons(d2, Cons(d3, Nil))))

#@ execution

d1 = dataset(data=[1.01, 1.03, 1.02, 1.04], scale=Interval)
d2 = dataset(data=[2.00, 2.03, 2.01, 2.05], scale=Interval)
d3 = dataset(data=[2.01, 2.02, 2.01, 2.05], scale=Interval)

print("p-value: %f" % ex_levene3(d1, d2, d3))
