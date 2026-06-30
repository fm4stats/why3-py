from statwhy import Nil, Cons, real
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

# Failed to verify the use of Fisher's method for combining 3 p-values to detect a risk.
def fail_meta_pvs_fisher(pv1 : real, pv2 : real, pv3 : real, observe_harm: formula) -> real :
    #@  requires \
    #@    let pvs  = Cons pv1 (Cons pv2 (Cons pv3 Nil)) in \
    #@    pvalues pvs /\ \
    #@    forall w' : world. (w' |= (Equiv indicate_risk (Impl disj_exps observe_harm)))

    #@  ensures \
    #@    pvalue result /\ \
    #@    (World !st interp |= StatB (Eq result) indicate_risk)

    pvs = Cons(pv1, Cons(pv2, Cons(pv3, Nil)))
    return exec_combine_pvs_fisher(pvs, exps, disj_exps, observe_harm)

#@ execution

# The p-values for the 3 experiments
pv1 : real = 0.1
pv2 : real = 0.2
pv3 : real = 0.3

# The dummy alternative hypothesis
fml = formula()

res = fail_meta_pvs_fisher(pv1, pv2, pv3, fml)
print("FAILED EXAMPLE: fail_meta_pvs_fisher p-value : %f" % res)
# FAILED EXAMPLE: fail_meta_pvs_fisher p-value : 0.115216
