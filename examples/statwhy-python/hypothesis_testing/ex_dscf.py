from statwhy import Nil, Cons, array, string, NormalD, UnknownD, Param, Const, real, Two, dataset, Interval
from statwhy import exec_steel_dscf

#@ use cameleerBHL.CameleerBHL
#@ use steel_dscf.Steel_DSCF
#@ use array.Array

p1 = UnknownD("p1")
p2 = UnknownD("p2")
p3 = UnknownD("p3")

def ex_dscf3(d1, d2, d3) -> array[real] :
    #@ requires \
    #@          let t_mu1 = RealT (mean p1) in \
    #@          let t_mu2 = RealT (mean p2) in \
    #@          let t_mu3 = RealT (mean p3) in \
    #@          let terms3 = (Cons t_mu1 (Cons t_mu2 (Cons t_mu3 Nil))) in \
    #@          !st = Nil /\ \
    #@          d1.scale = d2.scale = d3.scale = Interval /\ \
    #@          for_all2 \
    #@            sampled \
    #@            (Cons d1 (Cons d2 (Cons d3 Nil))) \
    #@            (Cons p1 (Cons p2 (Cons p3 Nil))) /\ \
    #@          (World !st interp)|= eq_variance p1 p2 /\ \
    #@          (World !st interp)|= eq_variance p2 p3 /\ \
    #@          for_all (fun fml -> (World !st interp) |= Possible fml) (combinations terms3 "<") /\ \
    #@          for_all (fun fml -> (World !st interp) |= Possible fml) (combinations terms3 ">")
    #@  ensures \
    #@    let t_mu1 = RealT (mean p1) in \
    #@    let t_mu2 = RealT (mean p2) in \
    #@    let t_mu3 = RealT (mean p3) in \
    #@    let terms3 = (Cons t_mu1 (Cons t_mu2 (Cons t_mu3 Nil))) in \
    #@    let ps = result in \
    #@    for_all (fun t -> let (i,fml) = t in \
    #@              (Eq (ps[i]) = compose_pvs fml !st) && \
    #@              (World !st interp |= StatB (Eq (ps[i])) fml)) \
    #@            (enumerate (combinations terms3 "!=") 0)

    return exec_steel_dscf(Cons(p1, Cons(p2, Cons(p3, Nil))), Cons(d1, Cons(d2, Cons(d3, Nil))))

#@ execution

# The values are taken from the manual of scikit_posthocs.posthoc_dscf.
# https://scikit-posthocs.readthedocs.io/en/latest/generated/scikit_posthocs.posthoc_dscf.html
y1 = dataset(data=[1,2,3,5,1], scale=Interval)
y2 = dataset(data=[12,31,54,62,12], scale=Interval)
y3 = dataset(data=[10,12,6,74,11], scale=Interval)

result = ex_dscf3(y1, y2, y3)
print("p-value between y1 and y2: %f" % result[0])
print("p-value between y1 and y3: %f" % result[1])
print("p-value between y2 and y3: %f" % result[2])
