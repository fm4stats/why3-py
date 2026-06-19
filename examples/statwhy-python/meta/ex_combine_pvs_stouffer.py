from statwhy import Nil, Cons, array, string, NormalD, UnknownD, Param, Const, real, Two
from statwhy import formula, Disj, sit
from statwhy import exec_combine_pvs_stouffer_Two
from statwhy import exec_combine_pvs_stouffer_One
from statwhy import exec_combine_pvs_weighted_stouffer_Two
from statwhy import exec_combine_pvs_weighted_stouffer_One

#@ use cameleerBHL.CameleerBHL
#@ use combine_pvs.CombinePVs
#@ use list.Map

# The ID numbers for 3 experiments
exp1 : real = 1.0
exp2 : real = 2.0
exp3 : real = 3.0
exps : list[real] = Cons(exp1, Cons(exp2, Cons(exp3, Nil)))

# The disjunctive formula representing one of the three situations
disj_exps : formula = Disj(sit(exp1), Disj(sit(exp2), sit(exp3)))

# Executes Stouffer's method for combining 3 two-sided p-values.
def ex_combine_pvs_stouffer_Two(pv1: real, pv2 : real, pv3 : real, fml: formula) -> real :
    #@  requires \
    #@    let pvs = Cons pv1 (Cons pv2 (Cons pv3 Nil)) in \
    #@    difficult_to_define_appropriate_weights /\ \
    #@    let d : dataset real = { data = pvs; scale = Interval } in \
    #@    sampled d uniform_pv /\ (* Each p-value in d is sampled uniformly & independently. *) \
    #@    length pvs > 0 /\ \
    #@    pvalues pvs /\ \
    #@    for_all2 (fun pv exp -> (exists w' : world. w' |= StatB (Eq pv) (Conj (sit exp) fml))) pvs exps
    #      The statistical belief under the situation (sit exp) where each experiment exp has done.

    #@  ensures \
    #@    let result_pv = twice_pvalue result in \
    #@    pvalue result_pv /\ \
    #@    (World !st interp |= StatB (Eq result_pv) fml)

    pvs = Cons(pv1, Cons(pv2, Cons(pv3, Nil)))
    return exec_combine_pvs_stouffer_Two(pvs, exps, disj_exps, fml)

# Executes Stouffer's method for combining 3 upper-sided p-values.
def ex_combine_pvs_stouffer_Up(pv1: real, pv2 : real, pv3 : real, fml: formula) -> real :
    #@  requires \
    #@    let pvs = Cons pv1 (Cons pv2 (Cons pv3 Nil)) in \
    #@    difficult_to_define_appropriate_weights /\ \
    #@    let d : dataset real = { data = pvs; scale = Interval } in \
    #@    sampled d uniform_pv /\ (* Each p-value in d is sampled uniformly & independently. *) \
    #@    length pvs > 0 /\ \
    #@    pvalues pvs /\ \
    #@    for_all2 (fun pv exp -> (exists w' : world. w' |= StatB (Eq pv) (Conj (sit exp) fml))) pvs exps

    #@  ensures \
    #@    pvalue result /\ \
    #@    (World !st interp |= StatB (Eq result) fml)

    pvs = Cons(pv1, Cons(pv2, Cons(pv3, Nil)))
    return exec_combine_pvs_stouffer_One(pvs, exps, disj_exps, fml)

# Executes Stouffer's method for combining 3 lower-sided p-values.
def ex_combine_pvs_stouffer_Low(pv1 : real, pv2 : real, pv3 : real, fml: formula) -> real :
    #@  requires \
    #@    let pvs = Cons pv1 (Cons pv2 (Cons pv3 Nil)) in \
    #@    difficult_to_define_appropriate_weights /\ \
    #@    let d : dataset real = { data = pvs; scale = Interval } in \
    #@    sampled d uniform_pv /\ (* Each p-value in d is sampled uniformly & independently. *) \
    #@    length pvs > 0 /\ \
    #@    pvalues pvs /\ \
    #@    for_all2 (fun pv exp -> (exists w' : world. w' |= StatB (Eq pv) (Conj (sit exp) fml))) pvs exps

    #@  ensures \
    #@    pvalue result /\ \
    #@    (World !st interp |= StatB (Eq result) fml)

    pvs = Cons(pv1, Cons(pv2, Cons(pv3, Nil)))
    return exec_combine_pvs_stouffer_One(pvs, exps, disj_exps, fml)

# **********************************************************

# Executes weighted Stouffer's method for combining 3 two-sided p-values.
# The square root of the sample size is used as the weight.
def ex_combine_pvs_weighted_stouffer_Two(pv1 : real, size1 : int, pv2 : real, size2 : int, pv3 : real, size3 : int, fml: formula) -> real :
    #@  requires \
    #@    let pvs = Cons pv1 (Cons pv2 (Cons pv3 Nil)) in \
    #@    let ss  = Cons size1 (Cons size2 (Cons size3 Nil)) in \
    #@    not difficult_to_define_appropriate_weights /\ \
    #@    let d : dataset real = { data = pvs; scale = Interval } in \
    #@    sampled d uniform_pv /\ (* Each p-value in d is sampled uniformly & independently. *) \
    #@    length pvs > 0 /\ \
    #@    pvalues pvs /\ \
    #@    length ss > 0 /\ \
    #@    samplesizes ss /\ \
    #@    for_all2 (fun pv exp -> (exists w' : world. w' |= StatB (Eq pv) (Conj (sit exp) fml))) pvs exps

    #@  ensures \
    #@    let result_pv = twice_pvalue result in \
    #@    pvalue result_pv /\ \
    #@    (World !st interp |= StatB (Eq result_pv) fml)

    pvs = Cons(pv1, Cons(pv2, Cons(pv3, Nil)))
    ss = Cons(size1, Cons(size2, Cons(size3, Nil)))
    return exec_combine_pvs_weighted_stouffer_Two(pvs, exps, disj_exps, ss, fml)

# Executes weighted Stouffer's method for combining 3 upper-sided p-values.
# The square root of the sample size is used as the weight.
def ex_combine_pvs_weighted_stouffer_Up(pv1 : real, size1 : int, pv2 : real, size2 : int, pv3 : real, size3 : int, fml: formula) -> real :
    #@  requires \
    #@    let pvs = Cons pv1 (Cons pv2 (Cons pv3 Nil)) in \
    #@    let ss  = Cons size1 (Cons size2 (Cons size3 Nil)) in \
    #@    not difficult_to_define_appropriate_weights /\ \
    #@    let d : dataset real = { data = pvs; scale = Interval } in \
    #@    sampled d uniform_pv /\ (* Each p-value in d is sampled uniformly & independently. *) \
    #@    length pvs > 0 /\ \
    #@    pvalues pvs /\ \
    #@    length ss > 0 /\ \
    #@    samplesizes ss /\ \
    #@    for_all2 (fun pv exp -> (exists w' : world. w' |= StatB (Eq pv) (Conj (sit exp) fml))) pvs exps

    #@  ensures \
    #@    pvalue result /\ \
    #@    (World !st interp |= StatB (Eq result) fml)

    pvs = Cons(pv1, Cons(pv2, Cons(pv3, Nil)))
    ss = Cons(size1, Cons(size2, Cons(size3, Nil)))
    return exec_combine_pvs_weighted_stouffer_One(pvs, exps, disj_exps, ss, fml)

# Executes weighted Stouffer's method for combining 3 lower-sided p-values.
# The square root of the sample size is used as the weight.
def ex_combine_pvs_weighted_stouffer_Low(pv1 : real, size1 : int, pv2 : real, size2 : int, pv3 : real, size3 : int, fml: formula) -> real :
    #@  requires \
    #@    let pvs = Cons pv1 (Cons pv2 (Cons pv3 Nil)) in \
    #@    let ss  = Cons size1 (Cons size2 (Cons size3 Nil)) in \
    #@    not difficult_to_define_appropriate_weights /\ \
    #@    let d : dataset real = { data = pvs; scale = Interval } in \
    #@    sampled d uniform_pv /\ (* Each p-value in d is sampled uniformly & independently. *) \
    #@    length pvs > 0 /\ \
    #@    pvalues pvs /\ \
    #@    length ss > 0 /\ \
    #@    samplesizes ss /\ \
    #@    for_all2 (fun pv exp -> (exists w' : world. w' |= StatB (Eq pv) (Conj (sit exp) fml))) pvs exps

    #@  ensures \
    #@    pvalue result /\ \
    #@    (World !st interp |= StatB (Eq result) fml)

    pvs = Cons(pv1, Cons(pv2, Cons(pv3, Nil)))
    ss = Cons(size1, Cons(size2, Cons(size3, Nil)))
    return exec_combine_pvs_weighted_stouffer_One(pvs, exps, disj_exps, ss, fml)

#@ execution

# The 3 experiments' p-values
pv1 : real = 0.1
pv2 : real = 0.2
pv3 : real = 0.3
pvs = Cons(pv1, Cons(pv2, Cons(pv3, Nil)))

# The 3 experiments' samples sizes, which are used as weights
size1 : int = 10
size2 : int = 15
size3 : int = 20
ss = Cons(size1, Cons(size2, Cons(size3, Nil)))

# The dummy alternative hypothesis
fml = formula()

res = ex_combine_pvs_stouffer_Two(pv1, pv2, pv3, fml)
print("ex_combine_pvs_stouffer_Two p-value : %f" % res)

res = ex_combine_pvs_stouffer_Up(pv1, pv2, pv3, fml)
print("ex_combine_pvs_stouffer_Up p-value : %f" % res)

res = ex_combine_pvs_stouffer_Low(pv1, pv2, pv3, fml)
print("ex_combine_pvs_stouffer_Low p-value : %f" % res)

res = ex_combine_pvs_weighted_stouffer_Two(pv1, size1, pv2, size2, pv3, size3, fml)
print("ex_combine_pvs_weighted_stouffer_Two p-value : %f" % res)

res = ex_combine_pvs_weighted_stouffer_Up(pv1, size1, pv2, size2, pv3, size3, fml)
print("ex_combine_pvs_weighted_stouffer_Up p-value : %f" % res)

res = ex_combine_pvs_weighted_stouffer_Low(pv1, size1, pv2, size2, pv3, size3, fml)
print("ex_combine_pvs_weighted_stouffer_Low p-value : %f" % res)

