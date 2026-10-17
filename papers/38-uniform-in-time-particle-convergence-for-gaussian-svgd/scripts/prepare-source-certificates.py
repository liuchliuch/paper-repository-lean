#!/usr/bin/env python3
"""Deferred certificate materialization only. This program is not run by the proof session.
Public source contracts were independently written in Specification,
GeometrySpecification, SourceAffine and Production.Specification26/27. The
three sampling statements retain their explicit source-written signatures.
A final frozen source-hash check precedes materialization. No verification is
reported passed by this generator.
"""
import argparse,hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
A='Paper38.Main.AnalyticBaselines'
S='Paper38.Main.StatisticalBaselines'
REG=[
 ('theorem21',A+' → Paper38.Specification.Theorem21','Paper38.Main.theorem21'),
 ('theorem22',A+' → '+S+' → Paper38.Specification.Theorem22','Paper38.Main.theorem22'),
 ('proposition23',S+' → Paper38.Specification.Proposition23','Paper38.Main.proposition23'),
 ('theorem24',A+' → '+S+' → Paper38.Specification.Theorem24','Paper38.Main.theorem24'),
 ('corollary25',A+' → '+S+' → Paper38.Specification.Corollary25','Paper38.Main.corollary25'),
 ('proposition26',A+' → Paper38.Production.Specification26','Paper38.Main.proposition26'),
 ('corollary27',A+' → (∀ (Ω : Type u) [MeasurableSpace Ω] (d : ℕ), Paper38.ExternalEmpiricalTransport.RawEmpiricalStrongLaws Ω d) → (∀ d : ℕ, Paper38.ExternalEmpiricalTransport.QuadraticTransportSeparation d) → Paper38.Production.Specification27.{u}','Paper38.Main.corollary27'),
 ('lemma41',A+' → Paper38.GeometrySpecification.Lemma41','Paper38.Main.lemma41'),
 ('lemma42','Paper38.GeometrySpecification.Lemma42','Paper38.Main.lemma42'),
 ('proposition43',A+' → Paper38.GeometrySpecification.Proposition43','Paper38.Main.proposition43'),
 ('lemma51',A+' → Paper38.Specification.Lemma51','Paper38.Main.lemma51'),
 ('lemma61',A+' → Paper38.SourceAffine.Lemma61','Paper38.Main.lemma61'),
 ('lemma63',A+' → Paper38.SourceAffine.Lemma63','Paper38.Main.lemma63'),
 ('example91',A+' → '+S+' → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1/10 → Paper38.CosineSource.ExpectedConvergence ε','Paper38.Main.example91'),
]
LEGACY=[
 ('mobility_bilinear','MobilityBilinear'),('mobility_strict','MobilityStrict'),
 ('covariance_rank','CovarianceRank'),('covariance_span','CovarianceSpan'),
 ('endpoint_necessary','EndpointNecessary'),('density_affine_span','DensityAffineSpan'),
 ('particle_moment_closure','ParticleMomentClosure'),('standardized_residual','StandardizedResidual'),
 ('gaussian_mean_second_moment','GaussianMeanSecondMoment'),('affine_transport','AffineTransport'),
 ('finite_shape_floor','FiniteShapeFloor'),('physical_time_countability','PhysicalTimeCountability'),
 ('rate_dominates_mean','RateDominatesMean'),('scalar_counterexample','ScalarCounterexample'),
 ('cosine_hessian','CosineHessian'),('cosine_optimum','CosineOptimum'),
 ('density_positive_covariance','DensityPositiveCovariance'),('gaussian_synchronous','GaussianSynchronous'),
 ('quadratic_triangle','QuadraticTriangle')]
def frozen_sampling_type(name):
    source=(ROOT/'Paper38/SourceSamplingLemmas.lean').read_text()
    tail=source.split('theorem '+name+' ',1)[1]
    sig=tail.split(' := by',1)[0]
    depth=0
    for i,c in enumerate(sig):
        if c in '([{': depth+=1
        elif c in ')]}': depth-=1
        elif c==':' and depth==0:
            return '∀ {d : ℕ} '+sig[:i]+', '+sig[i+1:]
    raise ValueError('No explicit source contract for '+name)
def materialize():
    if (ROOT/'Verification/SourceStatements.lean').exists():
        raise SystemExit('Source fixtures already exist; preserve/review before intentional regeneration.')
    manifest=json.loads((ROOT/'Verification/preparation-inputs.json').read_text())
    for name,digest in manifest['files'].items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:
            raise SystemExit('Frozen source changed; review before certificate generation: '+name)
    reg=list(REG)
    for name in ('lemma62','lemma71','lemma72'):
        reg.append((name,frozen_sampling_type(name),'Paper38.SourceSamplingLemmas.'+name))
    for name,contract in LEGACY:
        reg.append(('legacy_'+name,'Paper38.Contracts.'+contract,'Paper38.Checked.'+name))
    prefix='import Paper38\nimport Verification.Statements\nnoncomputable section\nopen MeasureTheory Set\nopen scoped BigOperators Matrix MatrixOrder ENNReal NNReal\nopen Paper38.Model Paper38.Specification Paper38.ExternalStatisticalInputs\nuniverse u\n'
    statements=prefix+'namespace Paper38.SourceContracts\n'
    for name,ty,_ in reg: statements+='def '+name+' : Prop := '+ty+'\n\n'
    statements+='end Paper38.SourceContracts\n'
    (ROOT/'Verification/SourceStatements.lean').write_text(statements)
    for kind in ('Challenge','Solution'):
        imports='import Verification.SourceStatements\n'
        if kind=='Solution': imports+='import Verification.Solution\n'
        body=imports+'noncomputable section\nuniverse u\nnamespace Paper38.SourceChecked\n'
        for name,_,proof in reg:
            body+='theorem '+name+' : Paper38.SourceContracts.'+name+' := '+('by sorry' if kind=='Challenge' else proof)+'\n\n'
        body+='end Paper38.SourceChecked\n'
        (ROOT/('Verification/Source'+kind+'.lean')).write_text(body)
    (ROOT/'Verification/SourceNegativePremise.lean').write_text('import Verification.SourceStatements\nnamespace Paper38.SourceChecked\ntheorem theorem21 : False → Paper38.SourceContracts.theorem21 := fun h => h.elim\nend Paper38.SourceChecked\n')
    (ROOT/'Verification/SourceNegativeAxiom.lean').write_text('import Verification.SourceStatements\naxiom P38_source_unauthorized_control : Paper38.SourceContracts.theorem21\nnamespace Paper38.SourceChecked\ntheorem theorem21 : Paper38.SourceContracts.theorem21 := P38_source_unauthorized_control\nend Paper38.SourceChecked\n')
    for suffix,solution,names in [('comparator','Solution',[r[0] for r in reg]),('negative-premise','NegativePremise',['theorem21']),('negative-axiom','NegativeAxiom',['theorem21'])]:
        cfg={'challenge_module':'Verification.SourceChallenge','solution_module':'Verification.Source'+solution,'theorem_names':['Paper38.SourceChecked.'+n for n in names],'permitted_axioms':['propext','Classical.choice','Quot.sound'],'enable_nanoda':False}
        (ROOT/('Verification/source-'+suffix+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
    files=[ROOT/('Verification/Source'+name+'.lean') for name in ('Statements','Challenge','Solution','NegativePremise','NegativeAxiom')]
    files += [ROOT/('Verification/source-'+name+'.json') for name in ('comparator','negative-premise','negative-axiom')]
    review={'status':'materialized_pending_independent_review','input_files':manifest['files'],
      'target_count':len(reg),'files':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
    path=ROOT/'Verification/source-contracts-manifest.json'
    path.write_text(json.dumps(review,indent=2)+'\n')
    print('Prepared',len(reg),'frozen source/component comparisons; no Lean or Comparator checks executed.')
    print('Review the generated source-relative signatures, then check-reviewed '+hashlib.sha256(path.read_bytes()).hexdigest())
def check_reviewed(sha256):
    path=ROOT/'Verification/source-contracts-manifest.json'
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=sha256:
        raise SystemExit('Reviewed source-contract manifest SHA256 does not match')
    review=json.loads(path.read_text())
    baseline=json.loads((ROOT/'Verification/preparation-inputs.json').read_text())['files']
    if review['input_files']!=baseline:
        raise SystemExit('Preparation input inventory changed after materialization')
    for name,expected in {**baseline,**review['files']}.items():
        if not (ROOT/name).is_file() or hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=expected:
            raise SystemExit('Reviewed source or fixture changed: '+name)
    print('Reviewed hash matches unchanged source inputs and materialized fixtures; semantic review must already have occurred.')
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    stages=parser.add_subparsers(dest='stage',required=True)
    stages.add_parser('prepare',help='Materialize fixed source-relative contracts; performs no Lean build')
    review=stages.add_parser('check-reviewed',help='Check the exact SHA256 after independent source correspondence review')
    review.add_argument('sha256')
    args=parser.parse_args()
    if args.stage=='prepare':materialize()
    else:check_reviewed(args.sha256)
if __name__=='__main__': main()
