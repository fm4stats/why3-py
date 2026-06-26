from statwhy import real
from statwhy import Unspecified, dataset
from statwhy import Nil, Cons, Param, CategoricalD
from statwhy import exec_chi2_contingency

#@ use cameleerBHL.CameleerBHL
#@ use chi2_contingency.Chi2_contingency

p1 = Param("p1")
p2 = Param("p2")
p3 = Param("p3")
p4 = Param("p4")

p1d = Param("p1'")
p2d = Param("p2'")
p3d = Param("p3'")
p4d = Param("p4'")

p = CategoricalD(Cons(p1, Cons(p2, Cons(p3, Cons(p4, Nil)))))
pd = CategoricalD(Cons(p1d, Cons(p2d, Cons(p3d, Cons(p4d, Nil)))))

def ex_chi2_contingency(y1 : list[int], y2 : list[int], y3 : list[int], y4 : list[int]) -> real :
    #@ requires \
    #@          let h = Not (independent_dist p pd) in \
    #@          let ys = {data=(Cons y1 (Cons y2 (Cons y3 (Cons y4 Nil)))); scale=Unspecified} in \
    #@          is_empty !st /\ \
    #@          sampled2 ys p pd /\ \
    #@          length y1 = length y2 = length y3 = length y4 = 4 /\ \
    #@               for_all (for_all (fun y -> y >= 5)) (Cons y1 (Cons y2 (Cons y3 (Cons y4 Nil)))) /\ \
    #@          is_prob_dist (Cons p1 (Cons p2 (Cons p3 (Cons p4 Nil)))) (World !st interp) /\ \
    #@          is_prob_dist (Cons p1d (Cons p2d (Cons p3d (Cons p4d Nil)))) (World !st interp) /\ \
    #@          (World !st interp) |= Possible h

    #@ ensures \
    #@    let h = Not (independent_dist p pd) in \
    #@    let p = result in \
    #@    Eq p = compose_pvs h !st && \
    #@    (World !st interp) |= StatB (Eq p) h
    ys = dataset(data=Cons(y1, Cons(y2, Cons(y3, Cons(y4, Nil)))), scale=Unspecified)
    return exec_chi2_contingency(p, pd, ys, False)

#@ execution

y1 = [10, 20, 30]
y2 = [20, 60, 60]
y3 = [30, 80, 80]
y4 = [40, 80, 50]

print(ex_chi2_contingency(y1, y2, y3, y4))
