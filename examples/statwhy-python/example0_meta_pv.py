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

# Executes Fisher's method for combining 3 p-values to detect a risk.
def eg_meta_pvs_fisher(pv1 : real, pv2 : real, pv3 : real, observe_harm: formula) -> real :
    #@  requires \
    #@    let pvs  = Cons pv1 (Cons pv2 (Cons pv3 Nil)) in \
    #@    pvalues pvs /\ \
    #@    let d : dataset real = { data = pvs; scale = Interval } in \
    #@    sampled d uniform_pv /\ (* Each p-value in d is sampled uniformly & independently. *) \
    #@    intend_to_detect_excess_of_small_pv /\ \
    #@    forall w' : world. (w' |= (Equiv indicate_risk (Impl disj_exps observe_harm))) /\ (* decision rule *) \
    #@    (* The statistical belief on observe_harm under the situation (sit exp) where each experiment exp has done. *) \
    #@    for_all2 (fun pv exp -> (exists w' : world. w' |= StatB (Eq pv) (Impl (sit exp) observe_harm))) pvs exps

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

res = eg_meta_pvs_fisher(pv1, pv2, pv3, fml)
print("eg_meta_pvs_fisher p-value : %f" % res)
# eg_meta_pvs_fisher p-value : 0.115216
