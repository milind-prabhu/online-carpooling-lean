#!/usr/bin/env python3
"""Generate a self-contained PFR-style blueprint from compiled Lean dependencies.

Run from the project root after `lake env lean blueprint/Extract.lean`.
Graphviz is the only external rendering dependency. No browser/network is needed.
"""
from pathlib import Path
import collections, html, json, re, subprocess, textwrap

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / 'blueprint'
OUT = HERE / 'generated'
OUT.mkdir(exist_ok=True)
raw = {r['name']: r for r in json.loads((HERE/'compiled_dependencies.json').read_text())}
source = json.loads((HERE/'source_index.json').read_text())
records = {n: dict(raw[n], **source[n]) for n in source if n in raw}
raw_deps = {n: [d for d in r['used'] if d in raw and d != n] for n,r in raw.items()}

# These labels are exposition only. Every edge below is obtained from Lean expressions.
friendly = {
 'Move': 'Weighted Greedy move', 'Run': 'Legal Greedy run', 'Request': 'Weighted request',
 'uniformProb': 'Uniform finite probability',
 'topSum_step': 'Lemma 3.4 · Top-sum evolution', 'spreadness': 'Lemma 3.3 · Spreadness',
 'potential_bound': 'Lemma 3.2 · Potential bound', 'positive_cube_bound': 'Cubic discrepancy estimate',
 'lemma_3_1': 'Lemma 3.1 · Expanding moves', 'theorem_1_1': 'Theorem 1.1\nDeterministic upper bound',
 'lemma_4_2': 'Lemma 4.2 · Tree-like requests', 'tree_like_surplus_bound': 'Surplus-edge bound',
 'Run.component_witness': 'Component witness construction', 'Witness.spanning': 'Spanning-tree extraction',
 'Witness.families_card_bound': 'Witness counting · Eq. (6)',
 'occurrence_probability_bound': 'Occurrence probability · Eq. (7)',
 'stochastic_upper_tail': 'Basic stochastic tail', 'stochastic_refined_tail': 'Refined stochastic tail',
 'stochastic_basic_high_probability': 'Basic logarithmic threshold',
 'stochastic_refined_high_probability': 'Degree-dependent threshold',
 'theorem_1_2_basic_greedy': 'Theorem 1.2 · Basic\nStochastic upper bound',
 'theorem_1_2_refined_greedy': 'Theorem 1.2 · Refined\nStochastic upper bound',
 'equal_pair_of_bounded_integer_positions': 'Equal-position pigeonhole lemma',
 'equal_endpoint_lower_bound': 'Equal-endpoint potential argument',
 'adversarial_lower_bound_four_cubes': 'Adversarial cube-root lower bound',
 'selected_matching_probability': 'Adaptive prescription likelihood',
 'adaptive_prescription_amplification': 'Adaptive second-moment amplification',
 'scheduled_varying_targets_of_counts': 'Conditional lower bound\nInterleaved clique arrivals',
 'classCount_variance': 'Weighted occupancy variance',
 'fewPopulated_probability': 'Enough populated cliques',
 'weighted_cliques_lower_probability': 'Average over arrival schedules',
 'uniformProb_constant_fiber': 'Uniform sampling transfer',
 'exists_regular_graph': 'Regular remainder construction',
 'padding_parameters': 'All vertex counts · Padding arithmetic',
 'padded_graph_stochastic_lower': 'Unconditional padded-graph bound',
 'padded_graph_lower_logarithmic': 'Explicit logarithmic threshold',
 'cubic_log_rate': 'Real-log cube-root rate',
 'theorem_1_3': 'Theorem 1.3 / 4.3\nStochastic lower bound · All parameters',
 'theorem_1_3_with_error': 'Explicit vanishing-error modulus',
 'randomized_lower_bound': 'Randomized mixtures',
 'UnitOnlineRule': 'Causal online orientation rule',
 'StochasticLowerGuarantee': 'Precise lower-bound guarantee',
}
full = lambda n: 'Carpooling.'+n
overview_names = [full(n) for n in friendly if n not in {
 'Request','uniformProb','lemma_3_1','tree_like_surplus_bound','Witness.spanning',
 'stochastic_basic_high_probability','stochastic_refined_high_probability',
 'UnitOnlineRule','StochasticLowerGuarantee'}]
assert all(n in records for n in overview_names), set(overview_names)-records.keys()
mains = {full(n) for n in ['theorem_1_1','theorem_1_2_basic_greedy','theorem_1_2_refined_greedy','theorem_1_3']}

def displayed_dependencies(selected):
    """Nearest displayed dependencies, traversing omitted compiled helper constants."""
    selected = set(selected)
    edges, witnesses = set(), {}
    for target in sorted(selected):
        queue = collections.deque((d,[target,d]) for d in raw_deps.get(target,[]))
        seen = {target}
        while queue:
            dep,path = queue.popleft()
            if dep in seen: continue
            seen.add(dep)
            if dep in selected:
                edges.add((dep,target)); witnesses[(dep,target)] = list(reversed(path))
            else:
                queue.extend((d,path+[d]) for d in raw_deps.get(dep,[]) if d not in seen)
    return edges,witnesses

def reach(start,adj,skip=None):
    seen=set(); todo=[start]
    while todo:
        x=todo.pop()
        for y in adj.get(x,[]):
            if (x,y)==skip or y in seen: continue
            seen.add(y); todo.append(y)
    return seen

def reduce_edges(nodes,edges):
    """Remove redundant transitive arrows only for an acyclic displayed graph."""
    adj={n:[] for n in nodes}; indeg={n:0 for n in nodes}
    for a,b in edges: adj[a].append(b); indeg[b]+=1
    todo=[n for n in nodes if indeg[n]==0]; visited=0
    while todo:
        n=todo.pop(); visited+=1
        for b in adj[n]:
            indeg[b]-=1
            if not indeg[b]:todo.append(b)
    if visited!=len(nodes): return edges,False
    return {e for e in edges if e[1] not in reach(e[0],adj,skip=e)},True

node_ids={n:'decl_'+str(i) for i,n in enumerate(sorted(records))}
nodes={}
for n,r in records.items():
    short=n.removeprefix('Carpooling.')
    nodes[node_ids[n]]={
      'id':node_ids[n], 'name':n, 'label':friendly.get(short,short),
      'kind':'theorem' if raw[n]['kind']=='theorem' else 'definition',
      'statement':raw[n]['statement'], 'file':r['file'], 'line':r['line'],
      'source':r['source'], 'checked':True,
    }

views={
 'overview':('Main proof blueprint',overview_names),
 'deterministic':('Deterministic upper bound',[n for n,r in records.items() if Path(r['file']).stem in
    {'Basic','Requests','TopSums','Spreadness','Potential','Deterministic','UpperBounds'}]),
 'stochastic':('Stochastic upper bounds',[n for n,r in records.items() if Path(r['file']).stem in
    {'StochasticBasic','StochasticRefined','RefinedThresholds','RegularGraphs','Batched','RefinedBatched','StochasticTheorem',
     'WitnessCounting','RefinedWitnesses','WitnessCover','WitnessForest','TreeLike','LocalTreeLike','Components'}]),
 'lower':('Stochastic lower bound',[n for n,r in records.items() if Path(r['file']).stem in
    {'LowerBound','AdaptiveProbability','Amplification','Occupancy','WeightedOccupancy','CountBounds','WeightedLower',
     'UniformMaps','MixedSampling','GraphSums','RegularExistence','PaddedLower','PaddingParameters','PaddedThresholds',
     'OnlineLower','FinalLower','LowerCorollaries','VaryingSchedule','ChargedLower','PrefixCuts','Pushforward'}]),
 'full':('All source-named declarations',sorted(records)),
}
graph_data={}
for key,(title,chosen) in views.items():
    edges,paths=displayed_dependencies(chosen)
    edges,acyclic=reduce_edges(chosen,edges)
    edge_list=[{'from':node_ids[a],'to':node_ids[b],'path':paths[(a,b)]} for a,b in sorted(edges)]
    lines=['digraph proof {',
      'graph [rankdir=TB,bgcolor="white",pad="0.22",nodesep="0.24",ranksep="0.55",splines=polyline,outputorder=edgesfirst];',
      'node [fontname="DejaVu Sans",fontsize=10,style=filled,fillcolor="#b9e5b2",color="#23823c",fontcolor="#133b1e",penwidth=1.3,margin="0.13,0.08"];',
      'edge [color="#748076",arrowsize=0.65,penwidth=0.8];']
    for n in sorted(chosen):
        d=nodes[node_ids[n]]
        label=d['label'] if key=='overview' else n.removeprefix('Carpooling.')
        label='\n'.join('\n'.join(textwrap.wrap(part,width=35,break_long_words=True,break_on_hyphens=False)) for part in label.split('\n'))
        attrs={'id':d['id'],'label':label,'shape':'ellipse' if d['kind']=='theorem' else 'box',
          'tooltip':n+' — Lean-checked'}
        if n in mains: attrs.update(penwidth='2.5',peripheries='2',fillcolor='#8fd18b',fontsize='12')
        lines.append(json.dumps(n)+' ['+','.join(k+'='+json.dumps(v,ensure_ascii=False) for k,v in attrs.items())+'];')
    for a,b in sorted(edges): lines.append(json.dumps(a)+' -> '+json.dumps(b)+';')
    lines.append('}')
    dot=OUT/(key+'.dot');dot.write_text('\n'.join(lines))
    svg=OUT/(key+'.svg')
    subprocess.run(['dot','-Tsvg',str(dot),'-o',str(svg)],check=True)
    graph_data[key]={'title':title,'nodes':[node_ids[n] for n in sorted(chosen)],'edges':edge_list,
      'acyclic':acyclic,'svg':re.sub(r'^.*?(?=<svg\s)','',svg.read_text(),flags=re.S)}

data={'nodes':nodes,'views':graph_data,'main':[node_ids[n] for n in sorted(mains)],
      'audit_count':(ROOT/'Audit.lean').read_text().count('#print axioms'),
      'extraction':'Lean 4.24.0 compiled ConstantInfo types and values; omitted helper constants traversed; transitive redundant arrows removed when acyclic.',
      'raw_declaration_count':len(raw),'source_declaration_count':len(records),
      'foundational_axioms':['propext','Classical.choice','Quot.sound'],
      'inspiration':'https://teorth.github.io/pfr/blueprint/dep_graph_document.html'}
(OUT/'graph_data.json').write_text(json.dumps(data,ensure_ascii=False,indent=2))
template=(HERE/'template.html').read_text()
payload=json.dumps(data,ensure_ascii=False).replace('</','<\\/')
(OUT/'Online_Carpooling_Blueprint.html').write_text(template.replace('__GRAPH_DATA__',payload))
subprocess.run(['dot','-Tpdf',str(OUT/'overview.dot'),'-o',str(OUT/'Online_Carpooling_Dependency_Graph.pdf')],check=True)
subprocess.run(['dot','-Tpng','-Gdpi=110',str(OUT/'overview.dot'),'-o',str(OUT/'Online_Carpooling_Dependency_Graph.png')],check=True)
(OUT/'Online_Carpooling_Dependency_Graph.svg').write_text((OUT/'overview.svg').read_text())
print(json.dumps({'source_nodes':len(records),'overview_nodes':len(overview_names),
 'views':{k:{'nodes':len(v['nodes']),'edges':len(v['edges']),'acyclic':v['acyclic']} for k,v in graph_data.items()}},indent=2))
