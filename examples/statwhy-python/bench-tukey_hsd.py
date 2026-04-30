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

if len(sys.argv) != 3:
    print("Usage: bench-tukey_hsd.py TESTNAME NGROUPS", file=sys.stderr)
    print("Example: bench-tukey_hsd.py tukey_hsd 3", file=sys.stderr)
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

fargs = ", ".join(f"d{i}" for i in groups)
ml_mu_list = ml_list([f"t_mu{i}" for i in groups])
ml_n_list = ml_list([f"t_n{i}" for i in groups])
ml_d_list = ml_list([f"d{i} " for i in groups])
py_n_list = py_list([f"t_n{i}" for i in groups])
py_d_list = py_list([f"d{i}" for i in groups])

result = template.render(groups=groups,
                         fargs=fargs,
                         ml_mu_list=ml_mu_list,
                         ml_n_list=ml_n_list,
                         ml_d_list=ml_d_list,
                         py_n_list=py_n_list,
                         py_d_list=py_d_list)

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

match = re.search(r"<ide_info>interp command 'StatWhy[a-z_]*' wall-clock=([0-9.]+)", log)

if match:
    wall_clock1 = float(match.group(1))
else:
    raise RuntimeError("start-time not found")

matches = re.findall(r"<scheduler>schedule_proof_attempt\(callback\): s=Done\(.*\) wall-clock=([0-9.]+)", log)

if matches:
    wall_clock2 = float(matches[-1])
else:
    raise RuntimeError("end-time not found")

time = wall_clock2 - wall_clock1
print(f"testname={testname} ngroups={ngroups} time={time}")

#print(log)
