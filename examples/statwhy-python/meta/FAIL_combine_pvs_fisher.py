# This program's verification will be FAILED.

from statwhy import Nil, Cons, array, string, NormalD, UnknownD, Param, Const, real, Two
from statwhy import formula, Disj, sit
from statwhy import exec_combine_pvs_fisher

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

# Publication bias: inappropriate use of Fisher's method for combining 3 p-values.
# The verification of the following INCORRECT procedure will be FAILED.
def ex_combine_pvs_fisher(pv1: real, pv2 : real, pv3 : real, fml: formula) -> real :
    #@  requires \
    #@    let pvs = Cons pv1 (Cons pv2 (Cons pv3 Nil)) in \
    #@    intend_to_detect_excess_of_small_pv /\ \
    #@    let d : dataset real = { data = pvs; scale = Interval } in \
    #@    sampled d significant_pv /\ \
    #@      (* The verification fails here. \
    #@         The p-values in d are collected from only the published experiments showing significance. \
    #@         Then this will not satisfy a precondition for Fisher's method *) \
    #@    length pvs > 0 /\ \
    #@    pvalues pvs /\ \
    #@    for_all2 (fun pv exp -> (exists w' : world. w' |= StatB (Eq pv) (Conj (sit exp) fml))) pvs exps

    #@  ensures \
    #@    pvalue result /\ \
    #@    (World !st interp |= StatB (Eq result) (Conj  disj_exps fml))

    pvs = Cons(pv1, Cons(pv2, Cons(pv3, Nil)))
    return exec_combine_pvs_fisher(pvs, exps, disj_exps, fml)

#@ execution

# The p-values for the 3 experiments
pv1 : real = 0.1
pv2 : real = 0.2
pv3 : real = 0.3

# The dummy alternative hypothesis
fml = formula()

res = ex_combine_pvs_fisher(pv1, pv2, pv3, fml)
print("incorrect ex_combine_pvs_fisher p-value : %f" % res)
# p-value : 0.115216
