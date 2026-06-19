from statwhy import UnknownD, real, Two, Up, Low
from statwhy import distribution
from statwhy import ctable
from statwhy import exec_Mantel_Haenszel

#@ use cameleerBHL.CameleerBHL
#@ use combine_pvs.CombinePVs
#@ use meta_pvs_MantelHaenszel.PV_MetaAnalyses
#@ use list.Map

# Executes Mantel-Haenszel's method to combine 3 experiments with two-sided p-values.
def ex_Mantel_Haenszel_Two(dist : distribution, ys : list[ctable]) -> real :
    #@ requires \
    #@   is_empty !st /\ \
    #@   independently_sampled ys /\ (* The strata in ys are independent of each other. *) \
    #@   length ys > 0 /\ all_matrix2x2 ys /\ \
    #@   for_all (fun y -> \
    #@            let d = { data = y; scale = Interval } in \
    #@            sampled d dist) ys /\ \
    #@   for_all (fun t -> \
    #@            exists th : ctable.  (World !st interp) |= (odds_ratio th $= odds_ratio t)) \
    #@           ys /\ (* The odds ratios for all strata are identical. *) \
    #@   for_all (fun th -> \
    #@            ((World !st interp) |= Possible (odds_ratio th $< const_term 1.0) /\ \
    #@             (World !st interp) |= Possible (odds_ratio th $> const_term 1.0))) \
    #@           ys

    #@ ensures \
    #@   let pv = result in \
    #@   pvalue pv /\ \
    #@   let th = \
    #@     match ys with \
    #@     | Cons hd _ -> hd \
    #@     | Nil -> Nil \
    #@     end in \
    #@   Eq pv = compose_pvs (odds_ratio th $!= const_term 1.0) !st && \
    #@   (World !st interp) |= StatB (Eq pv) (odds_ratio th $!= const_term 1.0)

    return exec_Mantel_Haenszel(dist, ys, Two)

# Executes Mantel-Haenszel's method to combine 3 experiments with upper-sided p-values.
def ex_Mantel_Haenszel_Up(dist : distribution, ys : list[ctable]) -> real :
    #@ requires \
    #@   is_empty !st /\ \
    #@   independently_sampled ys /\ (* The strata in ys are independent of each other. *) \
    #@   length ys > 0 /\ all_matrix2x2 ys /\ \
    #@   for_all (fun y -> \
    #@            let d = { data = y; scale = Interval } in \
    #@            sampled d dist) ys /\ \
    #@   for_all (fun t -> \
    #@            exists th : ctable.  (World !st interp) |= (odds_ratio th $= odds_ratio t)) \
    #@           ys /\ (* The odds ratios for all strata are identical. *) \
    #@   for_all (fun th -> \
    #@            ((World !st interp) |= Not (Possible (odds_ratio th $< const_term 1.0)) /\ \
    #@             (World !st interp) |= Possible (odds_ratio th $> const_term 1.0))) \
    #@           ys

    #@ ensures \
    #@   let pv = result in \
    #@   pvalue pv /\ \
    #@   let th = \
    #@     match ys with \
    #@     | Cons hd _ -> hd \
    #@     | Nil -> Nil \
    #@     end in \
    #@   Eq pv = compose_pvs (odds_ratio th $> const_term 1.0) !st && \
    #@   (World !st interp) |= StatB (Eq pv) (odds_ratio th $> const_term 1.0)

    return exec_Mantel_Haenszel(dist, ys, Up)

# Executes Mantel-Haenszel's method to combine 3 experiments with lower-sided p-values.
def ex_Mantel_Haenszel_Low(dist : distribution, ys : list[ctable]) -> real :
    #@ requires \
    #@   is_empty !st /\ \
    #@   independently_sampled ys /\ (* The strata in ys are independent of each other. *) \
    #@   length ys > 0 /\ all_matrix2x2 ys /\ \
    #@   for_all (fun y -> \
    #@            let d = { data = y; scale = Interval } in \
    #@            sampled d dist) ys /\ \
    #@   for_all (fun t -> \
    #@            exists th : ctable.  (World !st interp) |= (odds_ratio th $= odds_ratio t)) \
    #@           ys /\ (* The odds ratios for all strata are identical. *) \
    #@   for_all (fun th -> \
    #@            ((World !st interp) |= Possible (odds_ratio th $< const_term 1.0) /\ \
    #@             (World !st interp) |= Not (Possible (odds_ratio th $> const_term 1.0)))) \
    #@           ys

    #@ ensures \
    #@   let pv = result in \
    #@   pvalue pv /\ \
    #@   let th = \
    #@     match ys with \
    #@     | Cons hd _ -> hd \
    #@     | Nil -> Nil \
    #@     end in \
    #@   Eq pv = compose_pvs (odds_ratio th $< const_term 1.0) !st && \
    #@   (World !st interp) |= StatB (Eq pv) (odds_ratio th $< const_term 1.0)

    return exec_Mantel_Haenszel(dist, ys, Low)

#@ execution

# example taken from the manual of statsmodels
# https://www.statsmodels.org/dev/examples/notebooks/generated/metaanalysis1.html

ctables = [[[18.0, 1.0], [12.0, 10.0]],
           [[22.0, 12.0], [12.0, 23.0]],
           [[21.0, 51.0], [15.0, 53.0]],
           [[14.0, 8.0], [5.0, 15.0]],
           [[42.0, 28.0], [13.0, 19.0]],
           [[80.0, 103.0], [33.0, 61.0]],
           [[13.0, 13.0], [18.0, 32.0]],
           [[37.0, 24.0], [30.0, 25.0]],
           [[23.0, 13.0], [12.0, 13.0]],
           [[19.0, 26.0], [14.0, 21.0]],
           [[106.0, 140.0], [76.0, 132.0]],
           [[170.0, 216.0], [46.0, 95.0]],
           [[34.0, 25.0], [17.0, 15.0]],
           [[18.0, 27.0], [3.0, 12.0]],
           [[13.0, 1.0], [14.0, 4.0]],
           [[12.0, 14.0], [10.0, 9.0]],
           [[42.0, 32.0], [40.0, 35.0]]]

res = ex_Mantel_Haenszel_Two(UnknownD("unknown"), ctables)
print("ex_Mantel_Haenszel_Two p-value : %f" % res)

res = ex_Mantel_Haenszel_Up(UnknownD("unknown"), ctables)
print("ex_Mantel_Haenszel_Up p-value : %f" % res)

res = ex_Mantel_Haenszel_Low(UnknownD("unknown"), ctables)
print("ex_Mantel_Haenszel_Low p-value : %f" % res)

