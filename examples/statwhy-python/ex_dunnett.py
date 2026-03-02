from statwhy import Nil, Cons, array, string, NormalD, Param, Const, real, Two
from statwhy import exec_dunnett

#@ use cameleerBHL.CameleerBHL
#@ use dunnett.Dunnett
#@ use array.Array

p0 = NormalD(Param("mu0"), Const(1.0))
p1 = NormalD(Param("mu1"), Const(1.0))
p2 = NormalD(Param("mu2"), Const(1.0))
p3 = NormalD(Param("mu3"), Const(1.0))

def ex_dunnett3(d1, d2, d3, c) -> array[real] :
    #@ requires for_all (fun d -> d.scale = Interval) \
    #@                   (Cons d1 (Cons d2 (Cons d3 Nil))) /\ \
    #@          independent_list \
    #@            (Cons d1 (Cons d2 (Cons d3 Nil))) /\ \
    #@          c.scale = Interval /\ \
    #@          !st = Nil /\ \
    #@          for_all2 \
    #@            sampled \
    #@            (Cons d1 (Cons d2 (Cons d3 Nil))) \
    #@            (Cons p1 (Cons p2 (Cons p3 Nil))) /\ \
    #@          sampled c p0 /\ \
    #@          for_all \
    #@            (fun p -> (World !st interp) |= Possible (mean p0 $< mean p) /\ \
    #@                      (World !st interp) |= Possible (mean p0 $> mean p)) \
    #@            (Cons p1 (Cons p2 (Cons p3 Nil)))

    #@  ensures \
    #@    let ps = result in \
    #@    for_all (fun t -> let (i,p) = t in \
    #@              (Eq (ps[i]) = compose_pvs (mean p0 $!= mean p) !st) && \
    #@              (World !st interp |= StatB (Eq (ps[i])) (mean p0 $!= mean p))) \
    #@            (enumerate (Cons p1 (Cons p2 (Cons p3 Nil))) 0)

    return exec_dunnett(Cons(p1, Cons(p2, Cons(p3, Nil))), p0, \
                        Cons(d1, Cons(d2, Cons(d3, Nil))), c, Two)
