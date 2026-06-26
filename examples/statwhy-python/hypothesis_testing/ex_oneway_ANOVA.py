from statwhy import Nil, Cons, array, string, NormalD, Param, real, Two, dataset, Interval
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

#@ execution

#from scipy.stats import norm
#for x in norm.rvs(loc=0.0, scale=1.0, size=10) :
#    print(x)
d1 = dataset(data=[
    -0.07937761449278029,
    0.047417278665964686,
    1.0434831830291018,
    2.654433206760891,
    0.7807048145108898,
    -1.054300419308777,
    1.4080905605511866,
    -0.4570151606922434,
    -0.8064697074315004,
    0.22057171958607324
], scale=Interval)

#from scipy.stats import norm
#for x in norm.rvs(loc=0.0, scale=1.0, size=10) :
#    print(x)
d2 = dataset(data=[
    -1.9346757593572415,
    1.4165696662456624,
    -2.0453092705287164,
    1.2216029461751674,
    -0.1253884998707974,
    1.2652737990403369,
    -1.6447465915968307,
    -1.1488584358016183,
    0.9787080889209674,
    1.0909360702407722
], scale=Interval)

#from scipy.stats import norm
#for x in norm.rvs(loc=0.0, scale=1.0, size=10) :
#    print(x)
d3 = dataset(data=[
    -0.01075137926677939,
    -0.7115830380267112,
    1.6390583048038454,
    -0.9097241196967417,
    1.1784213521683906,
    0.1311785796388489,
    1.5801104668006885,
    -1.356653709917324,
    0.4356146048899532,
    -1.2409875060865285
], scale=Interval)

print(ex_oneway_ANOVA(d1, d2, d3))


