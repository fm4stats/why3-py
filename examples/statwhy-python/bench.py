#!/usr/bin/python3

import re
import sys
import os
import tempfile
import subprocess
from functools import reduce
from jinja2 import Template

template_dict = {}

template_dict['tukey_hsd'] = r'''
from statwhy import Nil, Cons, string, NormalD, Param, real, Two, dataset, Interval
from statwhy import exec_tukey_hsd

#@ use cameleerBHL.CameleerBHL
#@ use tukey_HSD.Tukey_HSD
#@ use array.Array

{% for i in groups %}
t_n{{i}} = NormalD(Param("mu{{i}}"), Param("var"))
{% endfor %}

# Execute Tukey's HSD test for multiple comparison of groups
def ex_tukey_hsd({{fargs}}) :

    #@ requires \
{% for i in groups %}
    #@   let t_mu{{i}} = RealT (mean t_n{{i}}) in \
{% endfor %}
    #@   let terms = {{ml_mu_list}} in \
    #@   is_empty (!st) /\ \
    #@   independent_list {{ml_d_list}} /\ \
    #@   for_all2 \
    #@     sampled \
    #@     {{ml_d_list}} \
    #@     {{ml_n_list}} /\ \
    #@   for_all \
    #@     (fun d -> d.scale = Interval) \
    #@     {{ml_d_list}} /\ \
    #@   for_all (fun fml -> (World !st interp) |= Possible fml) (combinations terms "<") /\ \
    #@   for_all (fun fml -> (World !st interp) |= Possible fml) (combinations terms ">")

    #@ ensures \
{% for i in groups %}
    #@   let t_mu{{i}} = RealT (mean t_n{{i}}) in \
{% endfor %}
    #@   let terms = {{ml_mu_list}} in \
    #@   let ps = result in \
    #@   for_all (fun t -> let (i,fml) = t in \
    #@             (Eq (ps[i]) = compose_pvs fml !st) && \
    #@             (World !st interp |= StatB (Eq (ps[i])) fml)) \
    #@           (enumerate (combinations terms "!=") 0)

    return exec_tukey_hsd({{py_n_list}}, \
                          {{py_d_list}})
'''

template_dict['dunnett'] = r'''
from statwhy import Nil, Cons, array, string, NormalD, Param, Const, real, Two
from statwhy import exec_dunnett

#@ use cameleerBHL.CameleerBHL
#@ use dunnett.Dunnett
#@ use array.Array

p0 = NormalD(Param("mu0"), Const(1.0))
{% for i in groups %}
p{{i}} = NormalD(Param("mu{{i}}"), Const(1.0))
{% endfor %}

def ex_dunnett({{fargs}}, c) -> array[real] :
    #@ requires for_all (fun d -> d.scale = Interval) \
    #@                   {{ml_d_list}} /\ \
    #@          independent_list \
    #@            {{ml_d_list}} /\ \
    #@          c.scale = Interval /\ \
    #@          !st = Nil /\ \
    #@          for_all2 \
    #@            sampled \
    #@            {{ml_d_list}} \
    #@            {{ml_p_list}} /\ \
    #@          sampled c p0 /\ \
    #@          for_all \
    #@            (fun p -> (World !st interp) |= Possible (mean p0 $< mean p) /\ \
    #@                      (World !st interp) |= Possible (mean p0 $> mean p)) \
    #@            {{ml_p_list}}

    #@  ensures \
    #@    let ps = result in \
    #@    for_all (fun t -> let (i,p) = t in \
    #@              (Eq (ps[i]) = compose_pvs (mean p0 $!= mean p) !st) && \
    #@              (World !st interp |= StatB (Eq (ps[i])) (mean p0 $!= mean p))) \
    #@            (enumerate {{ml_p_list}} 0)

    return exec_dunnett({{py_p_list}}, p0, \
                        {{py_d_list}}, c, Two)
'''

template_dict['dscf'] = r'''
from statwhy import Nil, Cons, array, string, NormalD, UnknownD, Param, Const, real, Two, dataset, Interval
from statwhy import exec_steel_dwass

#@ use cameleerBHL.CameleerBHL
#@ use steel_dwass.Steel_Dwass
#@ use array.Array

{% for i in groups %}
p{{i}} = UnknownD("p{{i}}")
{% endfor %}

def ex_dscf({{fargs}}) -> array[real] :
    #@ requires \
{% for i in groups %}
    #@          let t_mu{{i}} = RealT (mean p{{i}}) in \
{% endfor %}
    #@          let terms = {{ml_mu_list}} in \
    #@          !st = Nil /\ \
    #@          {{eq_d_scale}} = Interval /\ \
    #@          for_all2 \
    #@            sampled \
    #@            {{ml_d_list}} \
    #@            {{ml_p_list}} /\ \
{% for i in groups[:-1] %}
    #@          (World !st interp)|= eq_variance p{{i}} p{{i+1}} /\ \
{% endfor %}
    #@          for_all (fun fml -> (World !st interp) |= Possible fml) (combinations terms "<") /\ \
    #@          for_all (fun fml -> (World !st interp) |= Possible fml) (combinations terms ">")
    #@  ensures \
{% for i in groups %}
    #@    let t_mu{{i}} = RealT (mean p{{i}}) in \
{% endfor %}
    #@    let terms = {{ml_mu_list}} in \
    #@    let ps = result in \
    #@    for_all (fun t -> let (i,fml) = t in \
    #@              (Eq (ps[i]) = compose_pvs fml !st) && \
    #@              (World !st interp |= StatB (Eq (ps[i])) fml)) \
    #@            (enumerate (combinations terms "!=") 0)

    # StatWhy's exec_steel_dwass can be used as DSCF test.
    return exec_steel_dwass({{py_p_list}}, {{py_d_list}})
'''

template_dict['bonferroni'] = r'''
from statwhy import string, NormalD, Param, real, exec_ttest_1samp, Two
#@ use cameleerBHL.CameleerBHL
#@ use ttest.Ttest

{% for i in groups %}
p{{i}} = NormalD(Param("mu{{i}}"), Param("var"))
{% endfor %}

def ex_bonferroni({{fargs}}) -> real :
    #@ requires \
{% for i in groups %}
    #@  d{{i}}.scale = Interval /\ \
    #@  sampled d{{i}} p{{i}} /\ \
    #@  (World !st interp) |= Possible (mean p{{i}} $< const_term {{i}}.0) /\ \
    #@  (World !st interp) |= Possible (mean p{{i}} $> const_term {{i}}.0) /\ \
{% endfor %}
    #@  is_empty !st

    #@ ensures \
    #@  let p = result in \
    #@  (Leq p) = compose_pvs \
    #@              ( \
{% for i in groups %}
    #@               {{ "$||" if not loop.first }} (mean p{{i}} $!= const_term {{i}}.0) \
{% endfor %}
    #@              ) !st && \
    #@  (World !st interp) |= StatB (Leq p) ( \
{% for i in groups %}
    #@                                       {{ "$||" if not loop.first }} (mean p{{i}} $!= const_term {{i}}.0) \
{% endfor %}
    #@                                      )

{% for i in groups %}
    r{{i}} = exec_ttest_1samp(p{{i}}, {{i}}.0, d{{i}}, Two)
{% endfor %}
    return {{py_add_r}}
'''

template_dict['combine_pvs_fisher'] = r'''
from statwhy import Nil, Cons, real
from statwhy import formula, Disj, sit
from statwhy import exec_combine_pvs_fisher

#@ use cameleerBHL.CameleerBHL
#@ use combine_pvs.CombinePVs
#@ use list.Map

# The ID numbers for experiments
{% for i in groups %}
exp{{i}} : real = {{i}}.0
{% endfor %}
exps : list[real] = {{py_exp_list}}

# The disjunctive formula representing one of the situations
disj_exps : formula = {{py_exp_disj}}

# Executes Fisher's method for combining p-values.

def ex_combine_pvs_fisher({{pv_fargs}}, fml: formula) -> real :
    #@  requires \
    #@    let pvs = {{ml_pv_list}} in \
    #@    pvalues pvs /\ \
    #@    let d : dataset real = { data = pvs; scale = Interval } in \
    #@    sampled d uniform_pv /\ (* Each p-value in d is sampled uniformly & independently. *) \
    #@    intend_to_detect_excess_of_small_pv /\ \
    #@    (* The statistical belief on fml under the situation (sit exp) where each experiment exp has done. *) \
    #@    for_all2 (fun pv exp -> (exists w' : world. w' |= StatB (Eq pv) (Impl (sit exp) fml))) pvs exps

    #@  ensures \
    #@    pvalue result /\ \
    #@    (World !st interp |= StatB (Eq result) (Impl disj_exps fml))

    pvs = {{py_pv_list}}
    return exec_combine_pvs_fisher(pvs, exps, disj_exps, fml)
'''

template_dict['combine_pvs_pearson'] = r'''
from statwhy import Nil, Cons, real
from statwhy import formula, Disj, sit
from statwhy import exec_combine_pvs_pearson

#@ use cameleerBHL.CameleerBHL
#@ use combine_pvs.CombinePVs
#@ use list.Map

# The ID numbers for experiments
{% for i in groups %}
exp{{i}} : real = {{i}}.0
{% endfor %}
exps : list[real] = {{py_exp_list}}

# The disjunctive formula representing one of the situations
disj_exps : formula = {{py_exp_disj}}

# Executes Pearson's method for combining p-values.
def ex_combine_pvs_pearson({{pv_fargs}}, fml: formula) -> real :
    #@    requires \
    #@      let pvs = {{ml_pv_list}} in \
    #@      pvalues pvs /\ \
    #@      let d : dataset real = { data = pvs; scale = Interval } in \
    #@      sampled d uniform_pv /\ (* Each p-value in d is sampled uniformly & independently. *) \
    #@      intend_to_detect_excess_of_large_pv /\ \
    #@      (* The statistical belief on fml under the situation (sit exp) where each experiment exp has done. *) \
    #@      for_all2 (fun pv exp -> (exists w' : world. w' |= StatB (Eq pv) (Impl (sit exp) fml))) pvs exps

    #@    ensures \
    #@      pvalue result /\ \
    #@      (World !st interp |= StatB (Eq result) (Impl disj_exps fml))

    pvs = {{py_pv_list}}
    return exec_combine_pvs_pearson(pvs, exps, disj_exps, fml)
'''

template_dict['combine_pvs_weighted_stouffer_Two'] = r'''
from statwhy import Nil, Cons, array, string, NormalD, UnknownD, Param, Const, real, Two
from statwhy import formula, Disj, sit
from statwhy import exec_combine_pvs_weighted_stouffer_Two

#@ use cameleerBHL.CameleerBHL
#@ use combine_pvs.CombinePVs
#@ use list.Map

# The ID numbers for experiments
{% for i in groups %}
exp{{i}} : real = {{i}}.0
{% endfor %}
exps : list[real] = {{py_exp_list}}

# The disjunctive formula representing one of the situations
disj_exps : formula = {{py_exp_disj}}

# Executes weighted Stouffer's method for combining two-sided p-values.
# The square root of the sample size is used as the weight.
def ex_combine_pvs_weighted_stouffer_Two({{pv_size_fargs}}, fml: formula) -> real :
    #@  requires \
    #@    let pvs = {{ml_pv_list}} in \
    #@    pvalues pvs /\ \
    #@    not difficult_to_define_appropriate_weights /\ \
    #@    let ss = {{ml_size_list}} in \
    #@    samplesizes ss /\ \
    #@    let d : dataset real = { data = pvs; scale = Interval } in \
    #@    sampled d uniform_pv /\ (* Each p-value in d is sampled uniformly & independently. *) \
    #@    for_all2 (fun pv exp -> (exists w' : world. w' |= StatB (Eq pv) (Impl (sit exp) fml))) pvs exps

    #@  ensures \
    #@    let result_pv = twice_pvalue result in \
    #@    pvalue result_pv /\ \
    #@    (World !st interp |= StatB (Eq result_pv) (Impl disj_exps fml))

    pvs = {{py_pv_list}}
    ss = {{py_size_list}}
    return exec_combine_pvs_weighted_stouffer_Two(pvs, exps, disj_exps, ss, fml)
'''

if len(sys.argv) != 3:
    print("Usage: python3 bench.py TESTNAME NGROUPS", file=sys.stderr)
    print("Example: python3 bench.py tukey_hsd 3", file=sys.stderr)
    print(f"Supported Tests: {" ".join(template_dict.keys())}", file=sys.stderr)
    sys.exit(1)

testname = sys.argv[1]
ngroups = int(sys.argv[2])

if not (testname in template_dict) :
    print(f"Invalid testname: {testname}", file=sys.stderr)
    sys.exit(1)

template = Template(template_dict[testname], trim_blocks=True, lstrip_blocks=True)

groups = range(1, 1 + ngroups)

def ml_list(l):
    return reduce(
        lambda acc, x: f"(Cons {x} {acc})",
        reversed(l),
        "Nil")

def py_list(l):
    return reduce(
        lambda acc, x: f"Cons({x}, {acc})",
        reversed(l),
        "Nil")

def py_disj(l):
    *l_except_last, last = l
    return reduce(
        lambda acc, x: f"Disj({x}, {acc})",
        reversed(l_except_last),
        last)

fargs = ", ".join(f"d{i}" for i in groups)
eq_d_scale = " = ".join(f"d{i}.scale" for i in groups)
ml_mu_list = ml_list([f"t_mu{i}" for i in groups])
ml_n_list = ml_list([f"t_n{i}" for i in groups])
ml_d_list = ml_list([f"d{i}" for i in groups])
ml_p_list = ml_list([f"p{i}" for i in groups])
py_add_r = " + ".join(f"r{i}" for i in groups)
py_n_list = py_list([f"t_n{i}" for i in groups])
py_d_list = py_list([f"d{i}" for i in groups])
py_p_list = py_list([f"p{i}" for i in groups])

py_exp_list = py_list([f"exp{i}" for i in groups])
py_exp_disj = py_disj([f"sit(exp{i})" for i in groups])
pv_fargs = ", ".join(f"pv{i} : real" for i in groups)
pv_aargs = ", ".join(f"pv{i}" for i in groups)
ml_pv_list = ml_list([f"pv{i}" for i in groups])
py_pv_list = py_list([f"pv{i}" for i in groups])
pv_size_fargs = ", ".join(f"pv{i} : real, size{i} : int" for i in groups)
ml_size_list = ml_list([f"size{i}" for i in groups])
py_size_list = py_list([f"size{i}" for i in groups])

result = template.render(groups=groups,
                         fargs=fargs,
                         eq_d_scale=eq_d_scale,
                         ml_mu_list=ml_mu_list,
                         ml_n_list=ml_n_list,
                         ml_d_list=ml_d_list,
                         ml_p_list=ml_p_list,
                         py_add_r=py_add_r,
                         py_n_list=py_n_list,
                         py_d_list=py_d_list,
                         py_p_list=py_p_list,
                         py_exp_list=py_exp_list,
                         py_exp_disj=py_exp_disj,
                         pv_fargs=pv_fargs,
                         pv_aargs=pv_aargs,
                         ml_pv_list=ml_pv_list,
                         py_pv_list=py_pv_list,
                         pv_size_fargs=pv_size_fargs,
                         ml_size_list=ml_size_list,
                         py_size_list=py_size_list)

fp = tempfile.NamedTemporaryFile(mode='w+', prefix="statwhy-py-bench.", suffix=".py", delete=False, delete_on_close=False)
fp.write(result)
fp.write("\n")
fp.close()

#print(fp.name)

commandline = [
    "./env-why3",
    "why3",
    "ide",
    "--debug=ide_info",
    "--debug=scheduler",
    f"--extra-config={os.environ["HOME"]}/.statwhy.conf",
    fp.name
]
process_result = subprocess.run(commandline, capture_output=True, encoding='utf-8')

log = process_result.stderr

# search following lines. (schedule_proof_attempt may exist multiple times.  The last one should be choosen.)
#
# start-time:
# <ide_info>interp command 'StatWhy' wall-clock=1777529898.285422s
# <ide_info>interp command 'StatWhy_aggressive' wall-clock=1777532508.753370s
#
# end-time:
# <scheduler>schedule_proof_attempt(callback): s=Done(Valid (0.10s, 64683 steps)) wall-clock=1777533483.874670s
# <scheduler>schedule_proof_attempt(callback): s=Done(Timeout (5.00s, 235866 steps)) wall-clock=1777533485.377639s

match = re.search(r"<ide_info>interp command '(StatWhy[a-z_]*)' wall-clock=([0-9.]+)", log)

if match:
    strategy = match.group(1)
    wall_clock1 = float(match.group(2))
else:
    raise RuntimeError("start-time not found")

matches = re.findall(r"<scheduler>schedule_proof_attempt\(callback\): s=Done\(.*\) wall-clock=([0-9.]+)", log)

if matches:
    wall_clock2 = float(matches[-1])
else:
    raise RuntimeError("end-time not found")

time = wall_clock2 - wall_clock1
print(f"{testname},{ngroups},{strategy},{time}")

#print(log)
