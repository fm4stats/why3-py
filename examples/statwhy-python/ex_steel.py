from statwhy import Nil, Cons, array, string, UnknownD, Param, Const, real, Two
from statwhy import exec_steel

#@ use cameleerBHL.CameleerBHL
#@ use steel.Steel
#@ use array.Array

p0 = UnknownD("p0")
p1 = UnknownD("p1")
p2 = UnknownD("p2")
p3 = UnknownD("p3")

def ex_steel3(d1, d2, d3, c) -> array[real] :
    #@  requires   !st = Nil /\ \
    #@             for_all (fun d -> d.scale = Interval) \
    #@                     (Cons d1 (Cons d2 (Cons d3 Nil))) /\ c.scale = Interval /\ \
    #@             independent_list \
    #@               (Cons d1 (Cons d2 (Cons d3 Nil))) /\ \
    #@             for_all2 \
    #@               sampled \
    #@               (Cons d1 (Cons d2 (Cons d3 Nil))) \
    #@               (Cons p1 (Cons p2 (Cons p3 Nil))) /\ \
    #@             sampled c p0 /\ \
    #@             for_all \
    #@               (fun p -> (World !st interp) |= eq_variance p0 p) \
    #@               (Cons p1 (Cons p2 (Cons p3 Nil))) /\ \
    #@             for_all \
    #@               (fun p -> (World !st interp) |= Possible (mean p0 $< mean p) /\ \
    #@                         (World !st interp) |= Possible (mean p0 $> mean p)) \
    #@               (Cons p1 (Cons p2 (Cons p3 Nil)))
    #@  ensures \
    #@    let ps = result in \
    #@    for_all (fun t -> let (i,p) = t in \
    #@              (Eq (ps[i]) = compose_pvs (mean p0 $!= mean p) !st) && \
    #@              (World !st interp |= StatB (Eq (ps[i])) (mean p0 $!= mean p))) \
    #@            (enumerate (Cons p1 (Cons p2 (Cons p3 Nil))) 0)
    return exec_steel(Cons(p1, Cons(p2, Cons(p3, Nil))), p0, \
                      Cons(d1, Cons(d2, Cons(d3, Nil))), c, Two)
