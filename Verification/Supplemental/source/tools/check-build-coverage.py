#!/usr/bin/env python3
"""Check source-build coverage against actual Lean argv records and artifacts."""
from pathlib import Path
import argparse
import collections
import json


def compiled_sources(records):
    compiled = collections.defaultdict(list)
    for record in records:
        args = record['argv']
        if '-o' not in args or record.get('exit_code') != 0:
            continue
        sources = [arg for arg in args if arg.endswith('.lean')]
        if not sources:
            continue
        assert '--trust=0' in args, f"Missing trust=0: {sources}"
        assert record['lake_no_cache'] == 'true', f"Cache enabled: {sources}"
        assert record['lake_artifact_cache'] == 'false', f"Artifact cache enabled: {sources}"
        output = (Path(record['cwd']) / args[args.index('-o')+1]).resolve()
        for source in sources:
            path = (Path(record['cwd']) / source).resolve()
            compiled[str(path)].append({'output':str(output),'record_pid':record['pid']})
    return compiled


def require_coverage(expected, compiled, check_artifacts=True):
    for source in expected:
        matches = compiled.get(str(source.resolve()), [])
        assert matches, f'Missing successful source compilation: {source}'
        if check_artifacts:
            assert any(Path(m['output']).is_file() for m in matches), f'Missing compiled output: {source}'


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--audit-root',type=Path,default=Path('/srv/catalan-audit'))
    parser.add_argument('--proof-root',type=Path,default=Path('/srv/catalan-proof'))
    args=parser.parse_args()
    root=args.audit_root
    proof=args.proof_root
    record_files=list((root/'invocations').glob('*.json')) + list((proof/'.lake/lean-invocations').glob('*.json'))
    records=[json.loads(p.read_text()) for p in record_files]
    compiled=compiled_sources(records)
    mathlib=proof/'.lake/packages/mathlib'
    groups={
        'mathlib_library':[mathlib/'Mathlib.lean',*sorted((mathlib/'Mathlib').rglob('*.lean'))],
        'catalan_library':[proof/'Catalan.lean',*sorted((proof/'Catalan').rglob('*.lean'))],
        'vendor':[p for p in sorted((proof/'vendor/ClassFieldTheory/Lean4').rglob('*.lean'))],
    }
    for expected in groups.values(): require_coverage(expected,compiled)
    manifest=json.loads((proof/'lake-manifest.json').read_text())
    counts={}
    for package in manifest['packages']:
        base=(proof/'.lake/packages'/package['name']).resolve()
        counts[package['name']]=sum(Path(source).is_relative_to(base) for source in compiled)
    summary={'coverage_passed':True,'expected_source_counts':{k:len(v) for k,v in groups.items()},
        'successfully_compiled_source_counts_by_dependency':counts,
        'all_successful_compilations_trust_zero':True,
        'mathlib_and_lake_package_caches_disabled':True,
        'invocation_records':len(records),
        'unique_successfully_compiled_sources':len(compiled)}
    (root/'evidence/build-coverage.json').write_text(json.dumps(summary,indent=2)+'\n')
    (root/'evidence/compiled-source-inventory.json').write_text(json.dumps(compiled,sort_keys=True,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__': main()
