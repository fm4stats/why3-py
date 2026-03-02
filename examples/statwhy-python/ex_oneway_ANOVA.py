from statwhy import Nil, Cons, array, string, NormalD, Param, real, Two
from statwhy import exec_oneway_ANOVA

#@ use cameleerBHL.CameleerBHL
#@ use oneway_ANOVA.Oneway_ANOVA

p1 = NormalD(Param("m1"), Param("v"))
p2 = NormalD(Param("m2"), Param("v"))
p3 = NormalD(Param("m3"), Param("v"))

def ex_oneway_ANOVA(d1, d2, d3) -> real :
    # Executes oneway ANOVA for 3 population means
    #@  requires   \
    #@             let t_m1 = mean p1 in \
    #@             let t_m2 = mean p2 in \
    #@             let t_m3 = mean p3 in \
    #@             for_all (fun d -> d.scale = Interval) (Cons d1 (Cons d2 (Cons d3 Nil))) /\ \
    #@             independent_list (Cons d1 (Cons d2 (Cons d3 Nil))) /\ \
    #@             is_empty !st /\ \
    #@             for_all2 \
    #@               (fun p y -> sampled y p) \
    #@               (Cons p1 (Cons p2 (Cons p3 Nil))) \
    #@               (Cons d1 (Cons d2 (Cons d3 Nil))) /\ \
    #@             ((World !st interp) |= Possible (t_m1 $< t_m2)) /\ \
    #@             ((World !st interp) |= Possible (t_m1 $> t_m2)) /\ \
    #@             ((World !st interp) |= Possible (t_m1 $< t_m3)) /\ \
    #@             ((World !st interp) |= Possible (t_m1 $> t_m3)) /\ \
    #@             ((World !st interp) |= Possible (t_m2 $< t_m3)) /\ \
    #@             ((World !st interp) |= Possible (t_m2 $> t_m3))
    #@  ensures \
    #@    let t_m1 = mean p1 in \
    #@    let t_m2 = mean p2 in \
    #@    let t_m3 = mean p3 in \
    #@    let p = result in \
    #@    let h = (t_m1 $!= t_m2) $|| (t_m1 $!= t_m3) $|| (t_m2 $!= t_m3) in \
    #@    Eq p = compose_pvs h !st && \
    #@    (World !st interp) |= StatB (Eq p) h
    return exec_oneway_ANOVA(Cons(p1, Cons(p2, Cons(p3, Nil))), Cons(d1, Cons(d2, Cons(d3, Nil))))
