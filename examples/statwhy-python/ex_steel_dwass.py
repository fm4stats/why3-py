from statwhy import Nil, Cons, array, string, NormalD, UnknownD, Param, Const, real, Two
from statwhy import exec_steel_dwass

#@ use cameleerBHL.CameleerBHL
#@ use steel_dwass.Steel_Dwass
#@ use array.Array

p1 = UnknownD("p1")
p2 = UnknownD("p2")
p3 = UnknownD("p3")

def ex_steel_dwass3(d1, d2, d3) -> array[real] :
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

    return exec_steel_dwass(Cons(p1, Cons(p2, Cons(p3, Nil))), Cons(d1, Cons(d2, Cons(d3, Nil))))

