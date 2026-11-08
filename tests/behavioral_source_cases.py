"""Authored models and independent fixed observations for B01–B32."""
import copy
import hashlib

PROFILE='behavioral-0.5.7-candidate/v1'


def case(source,count,identities,live,*,refs=None,values=None,loop=None,query=None,width=4,interval=(0,1),supers=None):
    ids=[dict(id=0,type=0,parent=None)]+[dict(id=i,type=d,parent=p) for i,d,p in identities]
    refs=refs or [[] for _ in live]
    values=values or [{} for _ in live]
    def view(d,actual):
        if d==actual: return True
        sup=(supers or {}).get(actual)
        return sup is not None and view(d,sup)
    frames=[dict(live=[0,*xs],references=rs,values=[[r['id'],zs.get(r['id'],0)] for r in ids])
            for xs,rs,zs in zip(live,refs,values)]
    return dict(version='clafer-behavioral-source-case/1',source=source,query=query or dict(kind='model'),
        bounds=dict(version='clafer-behavioral-bounds/2',profile=PROFILE,objects=len(ids),bitwidth=width,
            minSteps=len(live),maxSteps=len(live),integers=dict(lower=interval[0],upper=interval[1]),
            declarations=[dict(id=d,size=sum(view(d,r['type']) for r in ids),exact=True) for d in range(count)]),
        candidate=dict(version='clafer-behavioral-trace/2',profile=PROFILE,root=0,length=len(live),
            loop=len(live)-1 if loop is None else loop,identities=ids,frames=frames))


def pattern(property,frames):
    return case('P ?\nS ?\nQ ?\nR ?\n['+property+']\n',5,
                [(i,i,0) for i in range(1,5)],
                [[i+1 for i,x in enumerate(f) if x] for f in frames])


def patterns():
    # Same independently specified witnesses as the accepted #77 native fixtures,
    # now through authored CLI, full finite observation and exact-clock fixation.
    for row,text in enumerate(('never P','sometime P','lonce P','always P','S must precede P','S must follow P')):
        for col,scope in enumerate(('',' before R',' after Q',' between Q and R',' after Q until R')):
            for good in (False,True):
                frames=[]
                for t in range(4):
                    p=(not good and t==1) if row==0 else (good and t==1) if row==1 else (
                        (t==1 if good else t in (0,2)) if row==2 else (good if row==3 else t==1))
                    s=good and ((row==4 and t==0) or (row==5 and t==2))
                    frames.append((p,s,t==0,t==3))
                for positive in (False,True):
                    body='('+text+scope+')'
                    prop='initially '+(body if positive else '!'+body)
                    yield f'pattern-{row}-{col}-{good}-{positive}', ['B26','B14','B29'], case_status(good==positive), pattern(prop,frames)


def case_status(satisfied): return 'satisfied' if satisfied else 'violated'


def features():
    for name,expression,good in (
        ('singleton','X (one root)',True),
        ('empty','X (no root)',False),
        ('capture','all r : root | X (r = root)',True),
        ('union','X ((root ++ A.parent) = root)',True)):
        yield 'root-'+name,['B06','B07','B09'],case_status(good),case(
            'A ?\n['+expression+']\n',2,[(1,1,0)],[[1],[]])
    for present in (False,True):
        for name,expression in (('navigation','some root.A'),('parent','A.parent = root')):
            yield f'root-{name}-{present}',['B06','B09'],case_status(present),case(
                'A ?\n[initially X ('+expression+')]\n',2,[(1,1,0)],[[],[1] if present else []])
    for good in (False,True):
        expression='root.P = this.parent && root = this.parent.parent' if good else 'no root.P'
        yield 'root-nested-'+str(good),['B06','B09','B15'],case_status(good),case(
            'P\n  A\n    [X ('+expression+')]\n',3,[(1,1,0),(2,2,1)],[[1,2]])
        expression='some root.P' if good else 'no root.P'
        source='P\n  A\n    assert [X ('+expression+')]\n'
        yield 'root-check-'+str(good),['B06','B27'],case_status(not good),case(
            source,3,[(1,1,0),(2,2,1)],[[1,2]],query=dict(kind='check',assertion=0))
        yield 'root-scenario-'+str(good),['B06','B28'],case_status(good),case(
            'P\n  A\n',3,[(1,1,0),(2,2,1)],[[1,2]],
            query=dict(kind='scenario',owner=2,source='[X ('+expression+')]'))
    ids=[(1,1,0),(2,2,1),(3,3,2)]
    for name,body,live,loop,good in (
        ('next','X error',[[1,2],[1,2,3]],1,True),
        ('next-false','X error',[[1,2]],0,False),
        ('event','F error',[[1,2],[1,2,3]],1,True),
        ('event-false','F error',[[1,2]],0,False),
        ('cancel','F error',[[1,2],[]],1,True),
        ('cancel-negated','!(F error)',[[1,2],[]],1,True),
        ('context-death','F error',[[1,2],[1]],1,False),
        ('reappear','F error',[[1,2],[],[1,2,3]],2,True),
        ('loop-next','X error',[[],[1,2],[1,2,3]],1,False),
        ('always','G error',[[1,2,3],[]],1,True),
        ('always-false','G error',[[1,2,3],[1,2]],1,False),
        ('until','(some error || no error) U error',[[1,2],[1,2,3]],1,True),
        ('until-false','(some error || no error) U error',[[1,2]],0,False),
        ('weak','(some error || no error) W error',[[1,2]],0,True),
        ('weak-false','some error W some error',[[1,2]],0,False),
        ('initial','initially error',[[],[1,2,3]],0,True),
        ('initial-false','initially error',[[1,2],[],[1,2,3]],0,False),
        ('finally','finally error',[[1,2,3],[]],0,True),
        ('finally-false','finally error',[[1,2],[]],0,False)):
        source='machine ?\n  ctx ?\n    error ?\n    ['+body+']\n'
        yield name,['B02','B03','B09','B10','B11','B12','B13','B14','B20','B21','B30'],case_status(good),case(source,4,ids,live,loop=loop)
    for mode,good in (('->>',True),('->',False)):
        source='Target\nabstract Ref '+mode+' Target\nport : Ref 2..2\n'
        yield 'inherited-'+('bag' if good else 'set'),['B01','B04','B06'],'satisfied' if good else 'violated',case(
            source,4,[(1,1,0),(2,3,0),(3,3,0)],[[1,2,3]],refs=[[[2,2,1],[2,3,1]]],supers={3:2})
    for live,good in (([1,2],True),([1,2,3],False),([1],False)):
        source='abstract xor Choice\n  a ?\nchosen : Choice\n  b ?\n'
        yield 'group-'+str(len(live)),['B01','B05'],case_status(good),case(source,5,[(1,3,0),(2,2,1),(3,4,1)],[live],supers={3:1})
    for inherited in (False,True):
        for modifier,change,good in (
            ('finaltarget','swap',True),('finalref','swap',False),('final','swap',False),
            ('finalref finaltarget','replace',True),('finaltarget finalref','replace',True),
            ('final','replace',False),('finaltarget','add',True),('finalref','add',True),
            ('final','add',False),('finalref','gap',True),('finaltarget','gap',False),
            ('finalref finaltarget','image',False),('finaltarget finalref','image',False)):
            source=('abstract '+modifier+' R ->> int\nr : R *\n' if inherited else modifier+' r ->> int *\n')
            d=2 if inherited else 1
            live={'swap':[[1,2],[1,2]],'replace':[[1],[2]],'add':[[1],[1,2]],'gap':[[1],[],[1]],'image':[[1],[1]]}[change]
            values={'swap':[{1:0,2:1},{1:1,2:0}],'replace':[{},{}],'add':[{},{}],
                    'gap':[{}, {},{1:1}],'image':[{}, {1:1}]}[change]
            yield f'modifier-{inherited}-{modifier}-{change}',['B04','B17','B18','B31'],case_status(good),case(
                source,d+1,[(1,d,0),(2,d,0)],live,values=values,width=3,supers={2:1} if inherited else {})
    for modifier,live,good in (('initial',[[1,2],[],[1,2]],True),('initial',[[1,2],[],[1]],False),
                               ('final',[[1,2],[],[1]],True),('final',[[1,2],[1]],False)):
        yield f'inherited-{modifier}-{good}',['B16','B17'],case_status(good),case(
            'abstract Parent\n  '+modifier+' flag ?\np : Parent ?\n',4,[(1,3,0),(2,2,1)],live,width=3,supers={3:1})
    for body,live,good in (('all x : A | X (x in A)',[[1],[1]],True),
                           ('all x : A | X (x in A)',[[1],[2]],False),
                           ('let x = A in X (x in A)',[[1],[2]],False)):
        yield 'capture-'+str(good)+'-'+body[:3],['B03','B07','B08'],case_status(good),case(
            'A ?\n['+body+']\n',2,[(1,1,0),(2,1,0)],live,width=3)
    for good in (False,True):
        yield 'equation-'+str(good),['B31','B32'],case_status(good),case('r ->> int = 1\n',2,[(1,1,0)],[[1],[1]],
            values=[{1:1},{1:1 if good else 0}])
        yield 'disjoint-'+str(good),['B08','B29'],case_status(good),case('A *\n[some disj x; y : A | x != y]\n',2,
            [(1,1,0),(2,1,0)],[[1,2] if good else [1]])
    for text,good in (('sum r = 2',True),('sum r = 1',False),('r = 1',True),
                      ('product r = 1',True),('min r = 1 && max r = 1',True),
                      ('(-3 / 2 = -1) && (-3 % 2 = -1)',True),('all x : 0 | some x',True),
                      ('#(r ++ r) = 1',True)):
        count=1 if text.startswith('#') else 2
        yield 'arithmetic-'+hashlib.sha256(text.encode()).hexdigest()[:8],['B08','B31'],case_status(good),case(
            f'r ->> int {count}..{count}\n['+text+']\n',2,[(i,1,0) for i in range(1,count+1)],
            [list(range(1,count+1))],values=[{i:1 for i in range(1,count+1)}],width=3)
    for query,live,good in ((dict(kind='model'),[[1]],True),
                          (dict(kind='check',assertion=0),[[1]],True),
                          (dict(kind='check',assertion=0),[[1,2]],False),
                          (dict(kind='scenario',source='[some A]',owner=1),[[1]],False),
                          (dict(kind='scenario',source='[some A]',owner=1),[[1,2]],True)):
        yield f'property-{query["kind"]}-{good}', ['B27','B28'],case_status(good),case(
            'P\n  A ?\n  assert [some A]\n',3,[(1,1,0),(2,2,1)],live,query=query)
    for good in (False,True):
        frames=[(True,False,True,False),(True,False,False,False),
                (False,good,False,True),(False,False,True,False)]
        yield 'chain-'+str(good),['B22','B23','B25'],case_status(good),pattern('initially (P -[Q]->> S -[R]-> Q)',frames)
        yield 'declaration-transition-'+str(good),['B22','B24'],case_status(good),case(
            'P ?\n  A ? --> B\n  B ?\n',4,[(1,1,0),(2,2,1),(3,3,1)],[[1,2],[1,3] if good else [1]])
    for prop,good in (('initially (sometime P)',True),('sometime P',False)):
        yield 'recurrence-'+str(good),['B15'],case_status(good),pattern(prop,[(False,False,False,False),(True,False,False,False),(False,False,False,False)])
    for good in (False,True):
        yield 'enum-'+str(good),['B19'],case_status(good),case('enum Colour = Red | Blue\n',4,
            [(1,2,0),(2,2,0),(3,3,0)],[[1,3],[1,3] if good else [2,3]],supers={2:1,3:1},width=3)
        source='A ?\n[initially (some A && X some A)]\n[all x : A | X no (x ** A)]\n'
        yield 'identity-budget-'+str(good),['B02','B03','B07','B30'],case_status(good),case(source,2,
            [(1,1,0),(2,1,0)] if good else [(1,1,0)],[[1],[2] if good else [1]],loop=0,width=3)
        yield 'nested-universal-'+str(good),['B27'],case_status(not good),case(
            'P 2..2\n  A ?\n  assert [some A]\n',3,[(1,1,0),(2,1,0),(3,2,1),(4,2,2)],
            [[1,2,3,4] if good else [1,2,3]],query=dict(kind='check',assertion=0))
        source=('Controller\n  xor state\n    Red ?\n    Green ?\n    Amber ?\n'
                '  reading ->> int = 1\n  [initially state.Red]\n'
                '  [state.Red --> state.Green]\n  [state.Green --> state.Amber]\n'
                '  [state.Amber --> state.Red]\n  assert [always one state]\n')
        yield 'controller-'+str(good),['B05','B15','B20','B22','B31','B32'],case_status(good),case(
            source,7,[(1,1,0),(2,2,1),(3,3,2),(4,4,2),(5,5,2),(6,6,1)],
            [[1,2,3,6],[1,2,4,6] if good else [1,2,3,6],[1,2,5,6]],values=[{6:1}]*3,loop=0)
