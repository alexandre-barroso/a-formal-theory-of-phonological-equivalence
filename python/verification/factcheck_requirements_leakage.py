from __future__ import annotations
import io, json, os, re, sys, itertools
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

CORE_MODULES = ["core.py", "evaluate.py", "strictness.py", "footprint.py",
                "generate.py", "regimes.py", "interaction.py", "productive.py",
                "indep_gua.py", "frag_gua.py", "frag_lith.py", "frag_auto.py",
                "multilocus.py", "search.py", "frag_arapaho.py", "frag_voice.py", "frag_accent.py", "frag_phase.py",
                "frag_abc.py",
                "frag_ocp.py", "frag_tn.py", "frag_turkish.py", "continuous.py",
                "learn.py", "frag_harmony.py", "frag_antigem.py", "frag_apocope.py", "frag_contact.py",
                "frag_morphaccent.py", "frag_nuer.py", "frag_stratal.py", "frag_sandhi.py", "frag_seq.py", "frag_redup.py", "frag_schwa.py"]

FORBIDDEN = [
    r"\bKazakh\b", r"\bKirghiz\b", r"\bSidamo\b", r"\bFaroese\b", r"\bIcelandic\b", r"syjek", r"kijar",
    r"Canari", r"\bBro[sś]\b", r"\bNazarov\b", r"\bpasos\b", r"\bAfar\b", r"\bTonkawa\b", r"\bTiberian\b", r"\bAkkadian\b", r"\bDamascene\b", r"\bChevak\b", r"\bIraqi\b",
    r"\bLiko\b", r"\bYaka\b", r"\bTutrugbu\b", r"\bTafi\b", r"\bMcCollum\b", r"\bHyman\b",
    r"\bWilson\b", r"\bMaasai\b", r"koN", r"áin", r"keb-ele", r"tigol", r"Gouskova", r"Russian",
    r"\bahe?t[ɔo]", r"af[ɪi]so", r"atʃijeli", r"kpejsi", r"wʊsʊs",
    r"abgauti", r"apiberti", r"atitaiki", r"\bG34a\b", r"\bG34b\b", r"\bN7\b",
    r"\bG37c\b", r"\bC24ei\b", r"\bOR38\b", r"\bC21b\b", r"\bC23UE\b",
    r"observations_", r"\ballowed\b", r"expected_regression",
    r"h[eé]ces", r"[eé]tʃes", r"n[oó][oó]hob", r"beb[ií]is", r"n[eé][ií]tʃ",
    r"benéétno", r"\bP4\b", r"\bL1\b", r"ATTESTED",
    r"\bAlderete\b", r"Cupe[ñn]o", r"\bJapanese\b", r"\bTokyo\b", r"k[oó]obe", r"\bkko\b", r"\bpp[oó]",
    r"yosida", r"nisimura", r"\bPoser\b", r"\bMelvold\b", r"\bBenua\b", r"\bTAF\b", r"abura", r"kawa",
    r"\bkolokol", r"\bwena", r"\bp[eé]-yax", r"OODom", r"OORec",
    r"\bNuer\b", r"\bMonich\b", r"\bNilotic\b", r"Gjers", r"\bBentiu\b", r"\bNasir\b", r"r[aǎâā]aan", r"j[eěèē]̤?eer",
    r"\bDinka\b", r"\bReid\b",
    r"\bHuai", r"\bDurvasula\b", r"\bMandarin\b", r"\bJianghuai\b", r"\bChinese\b",
    r"\bFrischoff\b", r"\bRasin\b", r"\bChangtin\b", r"\bHakka\b", r"\bCatalan\b", r"\bHijazi\b", r"\bLardil\b",
    r"\bTatar\b", r"\bGidabal\b", r"\bSlovak\b", r"\bJohnson\b", r"\bgahw\b", r"\bChen\b",
    r"\bTonkawa\b", r"\bGouskova\b", r"\bHoijer\b", r"\bKager\b", r"\bHamilton\b", r"\bkomo\b", r"\btopo\b", r"\bnaato\b", r"\byapece\b",
    r"\bFlemming\b", r"\bSmith\b", r"\bPater\b", r"\bFrench\b", r"\bbotte\b", r"\bveste\b", r"\bMaurice\b",
    r"\bNez\b", r"\bPerce\b", r"\bKiparsky\b", r"\bDeal\b", r"\bWolf\b", r"\bAoki\b", r"\bCrook\b", r"\bRude\b", r"\bSahaptin", r"\bhekiN\b", r"\bkuu\b", r"\bkii\b",
]
DOC_ONLY = re.compile(r"^\s*(#|\"\"\"|')")


def test_form_token_boundary():
    pattern = r"\bpp[oó]"
    assert pattern in FORBIDDEN
    for form in ('ppo', 'ppó', 'ppoo', '"ppoo"', "['ppó']"):
        assert re.search(pattern, form), form
    for code in ('support', 'supports', 'full_fixed_frame_support', 'direct_step_fixed_frame_support'):
        assert not re.search(pattern, code), code


def strip_docs(src: str) -> str:
    out, in_doc = [], False
    for line in src.splitlines():
        s = line.strip()
        if in_doc:
            if '"""' in s:
                in_doc = False
            continue
        if s.startswith('"""') or s.startswith("'''"):
            if s.count('"""') == 1 and s.count("'''") == 0:
                in_doc = True
            continue
        if s.startswith("#"):
            continue
        out.append(line)
    return "\n".join(out)


def test_source_name_removal():
    bad = []
    for m in CORE_MODULES:
        p = ROOT / "phonological_requirements" / m
        if not p.exists():
            continue
        code = strip_docs(p.read_text())
        for pat in FORBIDDEN:
            for hit in re.finditer(pat, code):
                bad.append((m, pat, code[max(0, hit.start() - 40):hit.end() + 20]))
    return bad


def test_no_observation_import():
    bad = []
    for m in CORE_MODULES:
        p = ROOT / "phonological_requirements" / m
        if not p.exists():
            continue
        code = strip_docs(p.read_text())
        if re.search(r"\bobservations\b", code):
            bad.append((m, "mentions the observation module"))
    return bad


def test_arapaho_without_observations():
    from fractions import Fraction
    from phonological_requirements.frag_arapaho import sigma, declarations, config, ALPHABET
    from phonological_requirements.search import bb_search

    class Sealed:
        def __getattr__(self, name):
            raise PermissionError(f"held output table read: {name}")

    saved = sys.modules.get("phonological_requirements.observations")
    sys.modules["phonological_requirements.observations"] = Sealed()
    try:
        W = dict(ID_SEG=5, ID_NUCLEAR=3, ID_CONT=2, ID_GLOTTAL=2, ID_DOR=1,
                 ID_ANT=1, ID_LAB=1, ID_NAS=1, ID_OBS=1, ID_FRONT=1,
                 ID_HIGH=1, ID_ROUND=1, ID_HTONE=1, MUT_DOR=8, MUT_ANT=8,
                 NOCODA=2, DEP=10, MAX=10, SYNC=0)
        D = declarations("duplicated")
        out = []
        for cid in ("CLUS1", "CLUS2", "RND1"):
            mi, _ = bb_search(sigma(), config(cid), D, W, Fraction(1, 8), ALPHABET)
            out.append((cid, len(mi)))
        return out, None
    except PermissionError as e:
        return [], str(e)
    finally:
        if saved is None:
            sys.modules.pop("phonological_requirements.observations", None)
        else:
            sys.modules["phonological_requirements.observations"] = saved


def test_held_output_leakage():
    from phonological_requirements import frag_gua as FG
    from phonological_requirements.evaluate import activation, coefficients, score

    class Sealed:
        def __getattr__(self, name):
            raise PermissionError(f"held output table read during evaluation: {name}")

    sealed = {"phonological_opacity.gua.observations": Sealed(), "phonological_requirements.observations": Sealed()}
    saved = {k: sys.modules.get(k) for k in sealed}
    sys.modules.update(sealed)
    try:
        from phonological_requirements.products import gua_products
        sg = FG.make_sigma(); D = FG.declarations("typed")
        total = 0
        for focal, prod in gua_products():
            ref = FG.struct_from_segments(prod.reference, prod.words, prod.phrase_of_word)
            acts = activation(sg, ref, D)
            for combo in itertools.product(FG.ALPHABET, repeat=len(focal)):
                st = list(prod.reference)
                for q, v in zip(focal, combo):
                    st[q] = v
                cur = FG.struct_from_segments(tuple(st), prod.words, prod.phrase_of_word)
                score(coefficients(sg, ref, cur, D, acts), FG.WEIGHTS, FG.LAMBDA)
                total += 1
        return total, None
    except PermissionError as e:
        return 0, str(e)
    finally:
        for k, v in saved.items():
            if v is None:
                sys.modules.pop(k, None)
            else:
                sys.modules[k] = v


if __name__ == "__main__":
    test_form_token_boundary()
    print("20.1 form-token boundary: 5 positive and 4 negative controls passed")
    bad = test_source_name_removal()
    print(f"20.1 source-name removal: {len(bad)} forbidden tokens in the core modules")
    for b in bad[:10]:
        print("   ", b)
    imp = test_no_observation_import()
    print(f"20.1 observation-table import: {len(imp)} core modules mention it")
    for b in imp:
        print("   ", b)
    n, err = test_held_output_leakage()
    print(f"20.2 held-output leakage: evaluated {n} candidates with every "
          f"observation file unreadable; error = {err}")
    ara, err2 = test_arapaho_without_observations()
    print(f"20.2 held-output leakage, Arapaho: {ara}; error = {err2}")
    raise SystemExit(1 if (bad or imp or err or err2 or not ara) else 0)
