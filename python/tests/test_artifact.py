from __future__ import annotations

import csv
import hashlib
import json
import sys
import tempfile
import unittest
import zipfile
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
PACKAGE = ROOT / "verification" / "python"
if str(PACKAGE) not in sys.path:
    sys.path.insert(0, str(PACKAGE))

from second_order_phonology.audit import PrivatePathFindings
from second_order_phonology.common import IgnoredDirectoryNames, ReadJson, ReadTsv, Sha256File
from second_order_phonology.data_build import BuildCanonicalData
from second_order_phonology.release import BuildManifest, CleanGenerated, DeterministicZip, ManifestFiles, ValidateArchive
from second_order_phonology.style import ValidatePythonStyle
from second_order_phonology.validation import LeanChecks


class ArtifactTests(unittest.TestCase):
    def test_exact_rational_serialization(self) -> None:
        values = [Fraction(1, 1), Fraction(3, 5), Fraction(3, 10), Fraction(1, 10), Fraction(0, 1)]
        serialized = [str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}" for value in values]
        self.assertEqual(serialized, ["1", "3/5", "3/10", "1/10", "0"])

    def test_registry_counts_and_bilingual_parity(self) -> None:
        results = ReadTsv(ROOT / "registry" / "result_registry.tsv")
        proof_goals = ReadTsv(ROOT / "registry" / "proof_goal_registry.tsv")
        claims = ReadTsv(ROOT / "registry" / "claim_budget.tsv")
        self.assertEqual(len(results), 68)
        self.assertEqual(len({row["result_id"] for row in results}), 68)
        self.assertEqual(len(proof_goals), 218)
        self.assertEqual(len({row["proof_goal_id"] for row in proof_goals}), 218)
        self.assertEqual(len(claims), 58)
        self.assertTrue(all(row["statement_en"] and row["statement_pt_BR"] for row in results))
        self.assertTrue(all(row["one_sentence_claim_en"] and row["one_sentence_claim_pt_BR"] for row in claims))
        english = {path.stem for path in (ROOT / "proofs" / "en" / "results").glob("*.tex")}
        portuguese = {path.stem for path in (ROOT / "proofs" / "pt_BR" / "results").glob("*.tex")}
        self.assertEqual(english, portuguese)
        self.assertEqual(english, {row["result_id"] for row in results})

    def test_continuous_hg_exact_anchors(self) -> None:
        report = ReadJson(ROOT / "verification" / "reports" / "python_continuous_hg.json")
        checks = {row["check"]: row for row in report["checks"]}
        self.assertEqual(checks["quadratic_first_zero"]["observed"], 4)
        self.assertEqual(checks["kazakh_profile"]["observed"], ["1", "3/5", "3/10", "1/10", "0", "0", "0"])
        self.assertEqual(checks["kyrgyz_continuum"]["observed"], "41/42")
        self.assertEqual(checks["kyrgyz_tenths"]["observed"], "1")

    def test_maxent_mass_and_order_results(self) -> None:
        maxent = ReadJson(ROOT / "verification" / "reports" / "python_maxent.json")
        maxent_checks = {row["check"]: row for row in maxent["checks"]}
        self.assertEqual(maxent_checks["candidate_merger_changes_mass"]["observed"], "1/2")
        self.assertEqual(maxent_checks["combined_mass_restores_law"]["observed"], "2/3")
        applications = ReadJson(ROOT / "verification" / "reports" / "python_applications.json")
        application_checks = {row["check"]: row for row in applications["checks"]}
        self.assertIn("goldrick_complete_counterexample", application_checks)
        self.assertEqual(application_checks["goldrick_complete_counterexample"]["status"], "PASS")

    def test_demonstration_totals(self) -> None:
        BuildCanonicalData()
        portuguese = ReadTsv(ROOT / "data" / "canonical" / "demonstrations" / "portuguese_decision_summary.tsv")
        english = ReadTsv(ROOT / "data" / "canonical" / "demonstrations" / "english_decision_summary.tsv")
        mandarin = ReadTsv(ROOT / "data" / "canonical" / "demonstrations" / "mandarin_decision_summary.tsv")
        readers = [row for row in portuguese if row["reader"] != "union_of_reduction_witnesses"]
        self.assertTrue(all(row["weak_positive_cells"] == "72" for row in readers))
        self.assertEqual({row["reader"]: row["strong_pass_cells"] for row in readers}, {"full": "17", "leave_flatness_out": "11", "leave_high_low_out": "16", "leave_zcr_out": "13"})
        english_totals = english[0]
        self.assertEqual(english_totals["scenarios"], "150")
        self.assertEqual(english_totals["aggregate_rows"], "300")
        self.assertEqual(english_totals["positive_median_cells"], "4200")
        self.assertEqual(english_totals["speaker_scenario_rows"], "14135")
        self.assertEqual(mandarin[-1]["matches"], "622")
        self.assertEqual(mandarin[-1]["counterexamples"], "13")
        self.assertEqual(mandarin[-1]["refusals"], "4")
        self.assertEqual(mandarin[-1]["clear_complex_final_retyped_as_match"], "4")

    def test_bibliography_one_to_one(self) -> None:
        manifest = ReadTsv(ROOT / "bibliography" / "reference_manifest.tsv")
        keys = [row["bibkey"] for row in manifest]
        filenames = [row["filename"] for row in manifest]
        self.assertEqual(len(keys), 173)
        self.assertEqual(len(set(keys)), 173)
        self.assertEqual(len(set(filenames)), 173)
        validation = ReadJson(ROOT / "bibliography" / "bibliography_validation.json")
        self.assertEqual((validation["biber"]["compile_errors"], validation["biber"]["compile_warnings"], validation["biber"]["provenance_errors"], validation["biber"]["provenance_warnings"]), (0, 0, 0, 0))

    def test_absolute_private_path_detection(self) -> None:
        self.assertEqual(PrivatePathFindings("public/path/file.tsv"), [])
        self.assertTrue(PrivatePathFindings("/" + "Volumes/private/project/file.tsv"))
        self.assertTrue(PrivatePathFindings("/" + "Users/private/project/file.tsv"))

    def test_lean_public_hygiene_contract(self) -> None:
        checks = {row["check"]: row for row in LeanChecks()}
        self.assertEqual(checks["lean_public_hygiene"]["status"], "PASS")

    def test_python_source_policy(self) -> None:
        report = ValidatePythonStyle()
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(report["finding_count"], 0)

    def test_canonical_generation_is_deterministic(self) -> None:
        BuildCanonicalData()
        first = {row["dataset"]: row["sha256"] for row in ReadTsv(ROOT / "data" / "dataset_manifest.tsv")}
        BuildCanonicalData()
        second = {row["dataset"]: row["sha256"] for row in ReadTsv(ROOT / "data" / "dataset_manifest.tsv")}
        self.assertEqual(first, second)

    def test_manifest_completeness(self) -> None:
        result = BuildManifest()
        rows = ReadTsv(ROOT / "ARTIFACT_MANIFEST.tsv")
        self.assertEqual(result["file_count"], len(rows))
        self.assertTrue(all((ROOT / row["path"]).is_file() for row in rows))
        self.assertTrue(all(Sha256File(ROOT / row["path"]) == row["sha256"] for row in rows))
        ignored = IgnoredDirectoryNames()
        self.assertFalse(any(Path(row["path"]).parts and Path(row["path"]).parts[0] in ignored for row in rows))

    def test_manifest_refuses_source_tree_symlinks(self) -> None:
        import second_order_phonology.release as release_module
        from unittest.mock import patch

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            target = root / "target.txt"
            target.write_text("content\n", encoding="utf-8")
            (root / "linked.txt").symlink_to(target)
            with patch.object(release_module, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "symbolic links are forbidden"):
                    ManifestFiles()

    def test_clean_removes_stale_release_state(self) -> None:
        import second_order_phonology.release as release_module
        from unittest.mock import patch

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            generated = [
                root / "ARTIFACT_MANIFEST.tsv",
                root / "MANIFEST.sha256",
                root / "release" / "second_order_phonology_artifact.zip",
                root / "release" / "second_order_phonology_artifact.zip.sha256",
            ]
            for path in generated:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("stale\n", encoding="utf-8")
            release_notes = root / "release" / "release_notes.md"
            release_notes.write_text("source material\n", encoding="utf-8")
            with patch.object(release_module, "ROOT", root):
                result = CleanGenerated()
            self.assertEqual(result["removed_entries"], len(generated))
            self.assertTrue(all(not path.exists() for path in generated))
            self.assertTrue(release_notes.is_file())

    def test_release_archive_clean_and_deterministic(self) -> None:
        archive, first_digest = DeterministicZip()
        first_bytes = archive.read_bytes()
        archive, second_digest = DeterministicZip()
        self.assertEqual(first_digest, second_digest)
        self.assertEqual(first_bytes, archive.read_bytes())
        validation = ValidateArchive(archive)
        self.assertEqual(validation["status"], "PASS")
        with zipfile.ZipFile(archive) as handle:
            ignored = IgnoredDirectoryNames()
            self.assertFalse(any(Path(name).parts and Path(name).parts[0] in ignored for name in handle.namelist()))
            self.assertTrue(all(information.date_time == (1980, 1, 1, 0, 0, 0) for information in handle.infolist()))
            self.assertTrue(all((information.external_attr >> 16) == 0o100644 for information in handle.infolist()))

    def test_archive_validation_rejects_noncanonical_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            archive = Path(temporary) / "metadata.zip"
            payloads = {
                "release/release_notes.md": b"notes\n",
                "release/release_notes.pt-BR.md": b"notas\n",
                "sample.txt": b"sample\n",
            }
            rows = [
                f"{name}\t{hashlib.sha256(data).hexdigest()}\t{len(data)}\tpackage_metadata\ttrue"
                for name, data in sorted(payloads.items())
            ]
            manifest = ("path\tsha256\tbytes\trole\tincluded_in_release\n" + "\n".join(rows) + "\n").encode("utf-8")
            checksums = "".join(
                f"{hashlib.sha256(data).hexdigest()}  {name}\n"
                for name, data in sorted(payloads.items())
            ).encode("utf-8")
            members = {"ARTIFACT_MANIFEST.tsv": manifest, "MANIFEST.sha256": checksums, **payloads}
            with zipfile.ZipFile(archive, "w") as handle:
                for name, data in sorted(members.items()):
                    information = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
                    information.external_attr = (0o100644 & 0xFFFF) << 16
                    if name == "sample.txt":
                        information.date_time = (2001, 1, 1, 0, 0, 0)
                        information.external_attr = (0o100600 & 0xFFFF) << 16
                    handle.writestr(information, data)
            validation = ValidateArchive(archive)
            categories = {row["category"] for row in validation["findings"]}
            self.assertIn("noncanonical_timestamp", categories)
            self.assertIn("noncanonical_mode", categories)

    def test_archive_validation_rejects_unsafe_members(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            archive = Path(temporary) / "unsafe.zip"
            payload = b"unsafe"
            digest = hashlib.sha256(payload).hexdigest()
            manifest = "path\tsha256\tbytes\trole\tincluded_in_release\n"
            manifest += f"../escape.txt\t{digest}\t{len(payload)}\tpackage_metadata\ttrue\n"
            checksums = f"{digest}  ../escape.txt\n"
            with zipfile.ZipFile(archive, "w") as handle:
                handle.writestr("../escape.txt", payload)
                handle.writestr("ARTIFACT_MANIFEST.tsv", manifest)
                handle.writestr("MANIFEST.sha256", checksums)
            validation = ValidateArchive(archive)
            self.assertEqual(validation["status"], "FAIL")
            self.assertIn("unsafe_entry", {row["category"] for row in validation["findings"]})


if __name__ == "__main__":
    unittest.main()
