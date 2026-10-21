"""Real Analyzer execution and a native runtime with no development tools mounted."""
import copy
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/oracles'))
import oracle


# [utest->req~compiler-cli~1]
# [utest->req~compiler-diagnostics~1]
class CLIExternalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        parent = oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE', tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        cls.output = Path(tempfile.mkdtemp(prefix='cli-external-', dir=parent))
        cls.exe = ROOT / '.lake/build/bin/clafer-compiler'
        sources = [ROOT/'Main.lean', ROOT/'ClaferCompiler/Driver.lean', Path(__file__),
                   ROOT/'tests/CLIOracle.java', ROOT/'scripts/oracles/AlloyTextBridge.java',
                   *sorted((ROOT/'ClaferCompiler/Driver').glob('*.lean')),
                   *sorted((ROOT/'tests/fixtures/cli').glob('*.json'))]
        for source in sources:
            dest = cls.output/'source'/source.relative_to(ROOT)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source,dest)
        oracle.write(cls.output/'source.json', {str(p.relative_to(ROOT)):oracle.digest(p) for p in sources})
        oracle.write(cls.output/'binary.json',oracle.digest(cls.exe))
        print(f'CLI runtime/Analyzer evidence: {cls.output}',flush=True)

    def run_recorded(self, name, command, *, cwd=None, env=None):
        oracle.write(self.output/(name+'-command.json'),list(map(str,command)))
        result = subprocess.run(list(map(str,command)),cwd=cwd or self.output,env=env,
                                capture_output=True,timeout=30)
        (self.output/(name+'-stdout.log')).write_bytes(result.stdout)
        (self.output/(name+'-stderr.log')).write_bytes(result.stderr)
        self.assertEqual(result.returncode,0,result.stderr)
        return result

    def test_api_maps_and_source_diagnostic_serialization(self):
        modules = ['ClaferCompiler.IR.Structural', 'ClaferCompiler.Driver', 'tests.Driver']
        modules += ['ClaferCompiler.Backend.Alloy.'+n for n in
                    ('Syntax','Bounds','Names','Parse','Print','Structural')]
        modules += ['ClaferCompiler.Frontend.'+n for n in ('Surface','Lexer','Parser')]
        modules += ['ClaferCompiler.Driver.'+n for n in ('Json','Diagnostic','Decode')]
        self.run_recorded('api-build',['lake','build',*['+'+m+':c.o' for m in modules]],cwd=ROOT)
        harness = self.output/'Harness.lean'
        harness.write_text('import tests.Driver\ndef main : IO Unit := ClaferCompiler.Tests.Driver.run\n')
        cfile = self.output/'Harness.c'
        exe = self.output/'api-tests'
        self.run_recorded('api-compile',['lake','env','lean',f'--root={self.output}',
                          '-c',cfile,harness],cwd=ROOT)
        self.run_recorded('api-link',['lake','env','leanc',cfile,
            *[ROOT/'.lake/build/ir'/(m.replace('.','/')+'.c.o.export') for m in modules],
            '-o',exe],cwd=ROOT)
        r = self.run_recorded('api-run',[exe],cwd=ROOT)
        result = json.loads(r.stdout)
        self.assertEqual(result['ids'],[100,7])
        text = result['text'].encode()
        for m in result['mappings']:
            self.assertEqual(text[m['startByte']:m['endByte']],m['name'].encode())
        source = next(m for m in result['mappings'] if m['name']=='cc8')
        self.assertEqual((source['displayName'],source['file'],source['sourceStart'],source['sourceEnd']),
                         ('résumé','example.cfr',2,10))
        d = result['diagnostic']
        self.assertEqual(d['primary'],dict(kind='source',file='é.cfr',startByte=5,endByte=5,line=2,column=2))
        self.assertEqual(d['version'],1)
        self.assertEqual(d['category'],'malformed')
        self.assertEqual(result['relatedDiagnostic']['related'],
                         [dict(kind='source',file='other.cfr',startByte=1,endByte=3)])

    def test_actual_analyzer_sat_unsat_and_reference_heads(self):
        api = oracle.adapters()
        tools = os.environ.get('CLAFER_ORACLE_TOOLS')
        self.assertTrue(tools, 'CLAFER_ORACLE_TOOLS is required')
        _, _, runtime = oracle.load_tools(tools, api)
        oracle.write(self.output/'analyzer-runtime.json',runtime['identity'])
        env = api['alloy_runtime'].java_env()
        self.run_recorded('javac',[runtime['java'].with_name('javac'),'--release','17',
            '-cp',runtime['jar'],'-d',self.output,
            ROOT/'scripts/oracles/AlloyTextBridge.java',ROOT/'tests/CLIOracle.java'],env=env)
        model = json.loads((ROOT/'tests/fixtures/cli/optional.json').read_text())
        bounds = json.loads((ROOT/'tests/fixtures/cli/bounds.json').read_text())
        cases = [('optional',copy.deepcopy(model),copy.deepcopy(bounds),True)]
        zero = copy.deepcopy(bounds); zero['declarations'][0].update(size=0,exact=True)
        cases.append(('zero-root',copy.deepcopy(model),zero,False))
        for mode in ('bag','set'):
            m = copy.deepcopy(model); b = copy.deepcopy(bounds)
            m['declarations'][1]['localBounds'] = dict(lower=1,upper=1)
            reference = copy.deepcopy(m['declarations'][1])
            reference.update(id=9,name='refs',reference=dict(kind=mode,target=7),
                             localBounds=dict(lower=2,upper=2))
            m['declarations'].append(reference)
            m['parentRanks'].append(1); m['superRanks'].append(0); m['unused'].append(False)
            b.update(objects=4,bitwidth=8)
            b['declarations'].append(dict(id=9,size=2,exact=True))
            cases.append((mode,m,b,mode=='bag'))
        for name,m,b,_ in cases:
            oracle.write(self.output/(name+'.json'),m)
            oracle.write(self.output/(name+'-bounds.json'),b)
            result = self.run_recorded('compile-'+name,[self.exe,'compile-ir',name+'.json',
                '--bounds',name+'-bounds.json','--output',name+'.als'])
            self.assertEqual((result.stdout,result.stderr),(b'',b''))
        self.run_recorded('analyzer',[runtime['java'],'-Xmx512m','-XX:ActiveProcessorCount=1',
            '-XX:+UseSerialGC','-cp',os.pathsep.join([str(self.output),str(runtime['jar'])]),
            'CLIOracle',*[row[0] for row in cases]],env=env)
        results = json.loads((self.output/'results.json').read_text())
        self.assertEqual([r['observation']['satisfiable'] for r in results],[row[3] for row in cases])
        self.assertEqual([r['ast']['bitwidth'] for r in results],[5,5,8,8])
        self.assertTrue(any(s[1] and s[2]==0 for s in results[1]['ast']['scopes']))
        for r in results:
            self.assertFalse(r['ast']['check'])
            self.assertEqual(r['observation']['options']['solver'],'sat4j')
            self.assertTrue(r['observation']['options']['noOverflow'])

    def test_runtime_without_toolchain_or_oracles(self):
        bwrap = shutil.which('bwrap')
        self.assertTrue(bwrap, 'Bubblewrap is required for runtime isolation')
        linked = self.run_recorded('ldd',['ldd',self.exe]).stdout.decode()
        self.assertNotIn('not found',linked)
        libraries = sorted(set(re.findall(r'(/[^\s()]+)',linked)))
        self.assertTrue(libraries)
        self.assertTrue(all(p.startswith(('/lib/','/lib64/','/usr/lib/')) for p in libraries))
        work = self.output/'isolated'; work.mkdir()
        for name in ['optional.json','bounds.json']:
            shutil.copyfile(ROOT/'tests/fixtures/cli'/name,work/name)
        # Construct an empty root. Only the ELF binary, its shared-library closure,
        # input/output directory and kernel devices are present; no host /usr or /home.
        command = [bwrap,'--unshare-user','--unshare-pid','--unshare-ipc','--unshare-uts',
                   '--die-with-parent','--clearenv',
                   '--setenv','PATH','/no-tools','--setenv','LANG','C',
                   '--ro-bind',self.exe,'/compiler','--bind',work,'/work',
                   '--dev','/dev','--proc','/proc','--chdir','/work']
        for path in libraries:
            command.extend(['--ro-bind',path,path])
        oracle.write(self.output/'runtime-libraries.json',{p:oracle.digest(Path(p)) for p in libraries})
        self.run_recorded('isolated-version',[*command,'/compiler','--version'])
        self.run_recorded('isolated-compile',[*command,'/compiler','compile-ir','optional.json',
                           '--bounds','bounds.json','--output','isolated.als'])
        self.run_recorded('host-compile',[self.exe,'compile-ir','optional.json','--bounds',
                           'bounds.json','--output','host.als'],cwd=work)
        self.assertEqual((work/'isolated.als').read_bytes(),(work/'host.als').read_bytes())
        self.assertFalse((work/'isolated.als').read_bytes()==b'')
