from typing import NamedTuple
from typing import Any
from typing import Literal

import numpy as np

from scipy.stats import ttest_1samp
from scipy.stats import ttest_rel
from scipy.stats import ttest_ind
from scipy.stats import binomtest
from scipy.stats import chisquare
from scipy.stats import chi2_contingency
from scipy.stats import bartlett
from scipy.stats import levene
from scipy.stats import alexandergovern
from scipy.stats import anderson
from scipy.stats import cramervonmises
from scipy.stats import tukey_hsd
from scipy.stats import dunnett
from scipy.stats import f_oneway

from scikit_posthocs import posthoc_dscf # type: ignore

from scipy.stats import combine_pvalues

import statsmodels.stats.api as smstats # type: ignore

# cameleer/statwhy/lib/logicalFormula.mlw
#   type scale =
#    | Nominal
#    | Ordinal
#    | Interval
#    | Rational
#    | Unspecified

class scale :
    pass

Nominal = scale()
Ordinal = scale()
Interval = scale()
Rational = scale()
Unspecified = scale()

# cameleer/statwhy/lib/logicalFormula.mlw
#   type dataset 'a = {
#    data: list 'a;
#    scale: scale
#  }

# examples/executable_examples/cameleerBHL.mli
# type 'a dataset = 'a list

class dataset[T](NamedTuple):
    data: list[T]
    scale: scale

#dataset = list

Nil : list[Any] = []

def Cons(x, xs) :
    return [x] + xs

array = list

string = str

parameter = string

real = float

# cameleer/statwhy/lib/logicalFormula.mlw
# type pvalue = Eq real | Leq real
class pvalue :
    pass

# cameleer/statwhy/lib/logicalFormula.mlw
# type real_number = Param parameter | Const real

# examples/executable_examples/cameleerBHL.mli
# type real_number = Param of parameter | Const of float

class real_number :
    pass

def Param(x : parameter) -> real_number :
    return real_number()

def Const(x : real) -> real_number :
    return real_number()

# cameleer/statwhy/lib/logicalFormula.mlw :
#
#  type distribution =
#    (* continuous *)
#    | NormalD real_number real_number                 (* NormalD mu var *)
#    | ExponentialD real_number real_number            (* ExponentialD loc scale *)
#    | LogisticD real_number real_number               (* LogisticD loc scale *)
#    | ContUniformD real_number real_number                (* ContUniformD loc scale *)
#    | GammaD real_number real_number real_number      (* GammaD a loc scale *)
#    (* | GumbelLD real_number real_number                (\* The left-skewed Gumbel distribution: GumbelLD loc scale *\) *)
#    (* | GumbelRD real_number real_number                (\* The left-skewed Gumbel distribution: GumbelLD loc scale *\) *)
#    (* | WeibullMinD real_number real_number real_number (\* WeibullMinD c loc scale *\) *)
#    (* discrete *)
#    | CategoricalD (list real_number)                 (* CategoricalD p_s *)
#    | PoissonD real_number real_number real_number    (* PoissonD mu loc scale *)
#    (* unknown *)
#    | UnknownD string

class distribution :
    pass

def NormalD(x1 : real_number, x2 : real_number) -> distribution :
    return distribution()

def BernoulliD(x : real_number) -> distribution :
    return distribution()

def CategoricalD(x : list[real_number]) -> distribution :
    return distribution()

def UnknownD(x : string) -> distribution :
    return distribution()

# type atomic_formula = Pred psymb (list term)

class atomic_formula :
    pass

# type formula = Atom atomic_formula | Not formula
#              | Conj formula formula | Disj formula formula
#              | Impl formula formula | Equiv formula formula
#              | Possible formula | Know formula
#              | StatTau pvalue formula | StatB pvalue formula

class formula :
    pass

def Atom(a : atomic_formula) -> formula :
    return formula()

def Not(f : formula) -> formula :
    return formula()

def Conj(f1 : formula, f2 : formula) -> formula :
    return formula()

def Disj(f1 : formula, f2 : formula) -> formula :
    return formula()

def Impl(f1 : formula, f2 : formula) -> formula :
    return formula()

def Equiv(f1 : formula, f2 : formula) -> formula :
    return formula()

def Possible(f : formula) -> formula :
    return formula()

def Know(f : formula) -> formula :
    return formula()

def StatTau(p : pvalue, f : formula) -> formula :
    return formula()

def StatB(p : pvalue, f : formula) -> formula :
    return formula()

# cameleer/statwhy/lib/statBHL.mlw
#
#   type alternative = Two | Up | Low

class alternative :
    def __init__(self, alt_string):
        self.alt_string = alt_string

Two = alternative("two-sided")
Up = alternative("greater")
Low = alternative("less")

# cameleer/statwhy/lib//ex_anderson.mlw
#   type null_dist = Norm | Expon | Logistic

class null_dist :
    nd_string: Literal["norm", "expon", "logistic"]
    def __init__(self, nd_string: Literal["norm", "expon", "logistic"]):
        self.nd_string = nd_string

Norm = null_dist("norm")
Expon = null_dist("expon")
Logistic = null_dist("logistic")


# cameleer/statwhy/lib/combine_pvs.mlw :
# type experiment = real
# let function sit (exp: experiment) : formula =
#    Atom (Pred "situation" (Cons (RealT (Real (Const exp))) Nil))

experiment = real

def sit(exp : experiment) -> formula :
    return formula()

def flatten(lists):
    result = []
    for n, l in enumerate(lists):
        result.extend(l[1+n:])
    return result

def exec_ttest_1samp(p : distribution, mu : real, y : dataset[real], alt : alternative) -> real :
    return float(ttest_1samp(y.data, mu, alternative=alt.alt_string).pvalue)

def exec_ttest_paired(d1 : distribution, d2 : distribution, y1 : dataset[real], y2 : dataset[real], alt=alternative) -> real :
    return float(ttest_rel(y1.data, y2.data, alternative=alt.alt_string).pvalue)

def exec_ttest_ind_eq(d1 : distribution, d2 : distribution, y1 : dataset[real], y2 : dataset[real], alt : alternative) -> real :
    return float(ttest_ind(y1.data, y2.data, equal_var=True, alternative=alt.alt_string).pvalue)

def exec_ttest_ind_neq(d1 : distribution, d2 : distribution, y1 : dataset[real], y2 : dataset[real], alt : alternative) -> real :
    return float(ttest_ind(y1.data, y2.data, equal_var=False, alternative=alt.alt_string).pvalue)

def exec_chisquare_test(p : distribution, qs : list[real], d : dataset[int]) -> real :
    n = sum(d.data)
    expected = [float(p) * n for p in qs]
    return float(chisquare(f_obs=d.data, f_exp=expected).pvalue)

def exec_chi2_contingency(d1 : distribution, d2 : distribution, yy : dataset[list[int]], correction : bool) -> real :
    return chi2_contingency(yy.data, correction).pvalue

def exec_ftest(p1 : distribution, p2 : distribution, d1 : dataset[real], d2 : dataset[real], alt : alternative) -> real:
    return float(bartlett(d1.data, d2.data).pvalue)

def exec_bartlett(ps : list[distribution], ds : list[dataset[real]]) -> real:
    return float(bartlett(*[d.data for d in ds]).pvalue)

def exec_levene(ps : list[distribution], ds : list[dataset[real]]) -> real:
    return float(levene(*[d.data for d in ds]).pvalue)

def exec_binom_test(d : distribution, p0 : real, y : dataset[int], alt : alternative) -> real:
    cnt = sum(y.data)
    size = len(y.data)
    return float(binomtest(k=cnt, n=size, p=p0, alternative=alt.alt_string).pvalue)

def exec_alexandergovern(ps : list[distribution], ds : list[dataset[real]]) -> real:
    return float(alexandergovern(*[d.data for d in ds]).pvalue)

def exec_anderson(p : distribution, d : dataset[real], nd : null_dist) -> real:
    return float(anderson(
                   d.data,
                   dist=nd.nd_string, # type: ignore[arg-type]
                   method="interpolate" # type: ignore[arg-type]
                ).pvalue) # type: ignore[attr-defined]

def exec_cramervonmises(p1 : distribution, p_null : distribution, d : dataset[real]) -> real:
    return float(cramervonmises(d.data, 'norm').pvalue)



def exec_tukey_hsd(d : distribution, xs : list[dataset[real]]) -> list[real] :
    result = tukey_hsd(*[x.data for x in xs])
    return flatten(result.pvalue.tolist())

def exec_dunnett(dists : list[distribution], control_dist : distribution, ys : list[dataset[real]], c : dataset[real], alt : alternative) -> array[real] :
    return [float(p) for p in dunnett(*[y.data for y in ys], control=c.data, alternative=alt.alt_string).pvalue]

def exec_steel_dwass(dists : list[distribution], ys : list[dataset[real]]) -> array[real] :
    return flatten(posthoc_dscf([y.data for y in ys]).values.tolist())

def exec_steel_dscf(dists : list[distribution], ys : list[dataset[real]]) -> array[real] :
    return flatten(posthoc_dscf([y.data for y in ys]).values.tolist())

def exec_steel(dists : list[distribution], control_dist : distribution, ys : list[dataset[real]], c : dataset[real], alt : alternative) -> array[real] :
    raise NotImplementedError

def exec_oneway_ANOVA(ds : list[distribution], ys : list[dataset[real]]) -> real :
    return float(f_oneway(*[y.data for y in ys]).pvalue)


def exec_combine_pvs_fisher(pvs : list[real], exps : list[experiment], disj_exp : formula, fml : formula) -> real :
    return combine_pvalues(pvs, method='fisher').pvalue

def exec_combine_pvs_pearson(pvs : list[real], exps : list[experiment], disj_exp : formula, fml : formula) -> real :
    return combine_pvalues(pvs, method='pearson').pvalue

def exec_combine_pvs_MudholkarGeorge(pvs : list[real], exps : list[experiment], disj_exp : formula, fml : formula) -> real :
    return combine_pvalues(pvs, method='mudholkar_george').pvalue

def exec_combine_pvs_stouffer_Two(pvs : list[real], exps : list[experiment], disj_exp : formula, fml : formula) -> real :
    pvs = [pv / 2.0 for pv in pvs]
    return combine_pvalues(pvs, method='stouffer').pvalue * 2

def exec_combine_pvs_stouffer_One(pvs : list[real], exps : list[experiment], disj_exp : formula, fml : formula) -> real :
    return combine_pvalues(pvs, method='stouffer').pvalue

def exec_combine_pvs_weighted_stouffer_Two(pvs : list[real], exps : list[experiment], disj_exp : formula, ss : list[int], fml : formula) -> real :
    pvs = [pv / 2.0 for pv in pvs]
    return combine_pvalues(pvs, method='stouffer', weights=ss).pvalue * 2

def exec_combine_pvs_weighted_stouffer_One(pvs : list[real], exps : list[experiment], disj_exp : formula, ss : list[int], fml : formula) -> real :
    return combine_pvalues(pvs, method='stouffer', weights=ss).pvalue

# cameleer/statwhy/lib/meta_pvs_MantelHaenszel.mlw
ctable = list[list[real]]
def exec_Mantel_Haenszel(dist : distribution, ys : list[ctable], alt : alternative) -> real :
    st = smstats.StratifiedTable(np.array(ys).transpose(1, 2, 0).astype(np.float64))
    return st.test_equal_odds().pvalue

