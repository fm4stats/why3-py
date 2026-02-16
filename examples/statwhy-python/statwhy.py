from scipy.stats import ttest_1samp
from scipy.stats import ttest_rel
from scipy.stats import ttest_ind
from scipy.stats import tukey_hsd

# cameleer/statwhy/lib/logicalFormula.mlw
#   type dataset 'a = {
#    data: list 'a;
#    scale: scale
#  }

# examples/executable_examples/cameleerBHL.mli
# type 'a dataset = 'a list
dataset = list

Nil = []

def Cons(x, xs) :
    return [x] + xs

string = str

parameter = string

real = float

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

# cameleer/statwhy/lib/statBHL.mlw
#
#   type alternative = Two | Up | Low

class alternative :
    def __init__(self, alt_string):
        self.alt_string = alt_string

Two = alternative("two-sided")
Up = alternative("greater")
Low = alternative("less")

def exec_ttest_1samp(p : distribution, mu : real, y : list[real], alt : alternative) -> real :
    return ttest_1samp(y, mu, alternative=alt.alt_string).pvalue

def exec_ttest_paired(d1 : distribution, d2 : distribution, y1 : list[real], y2 : list[real], alt=alternative) -> real :
    return ttest_rel(y1, y2, alternative=alt.alt_string).pvalue

def exec_ttest_ind_eq(d1 : distribution, d2 : distribution, y1 : list[real], y2 : list[real], alt : alternative) -> real :
    return ttest_ind(y1, y2, equal_var=True, alternative=alt.alt_string).pvalue

def exec_ttest_ind_neq(d1 : distribution, d2 : distribution, y1 : list[real], y2 : list[real], alt : alternative) -> real :
    return ttest_ind(y1, y2, equal_var=False, alternative=alt.alt_string).pvalue

def flatten(lists):
    result = []
    for n, l in enumerate(lists):
        result.extend(l[1+n:])
    return result

def exec_tukey_hsd(d : distribution, xs : list[real]) -> list[real] :
    result = tukey_hsd(*xs)
    return flatten(result.pvalue.tolist())
