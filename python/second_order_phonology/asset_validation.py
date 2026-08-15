from __future__ import annotations

import json
import xml.etree.ElementTree as ElementTree
from collections import Counter
from pathlib import Path
from typing import Any

from PIL import Image

from .common import ROOT, ReadTsv, Sha256File, WriteJson, WriteTsv


def SvgGeometry(path: Path) -> tuple[str, str, str]:
    root = ElementTree.parse(path).getroot()
    return root.attrib.get("viewBox", ""), root.attrib.get("width", ""), root.attrib.get("height", "")


def ValidateBilingualAssets() -> dict[str, Any]:
    findings: list[dict[str, str]] = []
    figure_rows = ReadTsv(ROOT / "registry" / "figure_manifest.tsv")
    table_rows = ReadTsv(ROOT / "registry" / "table_manifest.tsv")
    figure_pairs = Counter(row["figure_id"] for row in figure_rows)
    table_pairs = Counter(row["table_id"] for row in table_rows)
    figure_ledger: list[dict[str, Any]] = []
    for identifier in sorted(figure_pairs):
        pair = {row["locale"]: row for row in figure_rows if row["figure_id"] == identifier}
        if set(pair) != {"en", "pt_BR"}:
            findings.append({"asset_id": identifier, "category": "locale_pair", "detail": ";".join(sorted(pair))})
            continue
        source_hashes = {row["source_sha256"] for row in pair.values()}
        source_specs = {row["source_spec"] for row in pair.values()}
        source_data = {row["source_data"] for row in pair.values()}
        widths = {row["intended_width_mm"] for row in pair.values()}
        if len(source_hashes) != 1 or len(source_specs) != 1 or len(source_data) != 1 or len(widths) != 1:
            findings.append({"asset_id": identifier, "category": "pair_source_or_geometry", "detail": "localized rows differ outside text"})
        spec_path = ROOT / next(iter(source_specs))
        if not spec_path.is_file() or Sha256File(spec_path) not in source_hashes:
            findings.append({"asset_id": identifier, "category": "source_hash", "detail": next(iter(source_specs))})
        png_sizes: dict[str, tuple[int, int]] = {}
        svg_geometries: dict[str, tuple[str, str, str]] = {}
        for locale, row in pair.items():
            paths = {extension: ROOT / row[extension] for extension in ["svg", "pdf", "png"]}
            missing = [extension for extension, path in paths.items() if not path.is_file()]
            if missing:
                findings.append({"asset_id": f"{identifier}:{locale}", "category": "missing_render", "detail": ";".join(missing)})
                continue
            with Image.open(paths["png"]) as image:
                png_sizes[locale] = image.size
            svg_geometries[locale] = SvgGeometry(paths["svg"])
            if paths["pdf"].read_bytes()[:4] != b"%PDF":
                findings.append({"asset_id": f"{identifier}:{locale}", "category": "pdf_header", "detail": row["pdf"]})
            figure_ledger.append({"figure_id": identifier, "locale": locale, "source_spec": row["source_spec"], "source_sha256": row["source_sha256"], "png_width_px": png_sizes[locale][0], "png_height_px": png_sizes[locale][1], "svg_viewbox": svg_geometries[locale][0], "intended_width_mm": row["intended_width_mm"], "status": "PASS"})
        if len(set(png_sizes.values())) > 1:
            findings.append({"asset_id": identifier, "category": "png_dimensions", "detail": json.dumps(png_sizes, sort_keys=True)})
        if len(set(svg_geometries.values())) > 1:
            findings.append({"asset_id": identifier, "category": "svg_geometry", "detail": json.dumps(svg_geometries, sort_keys=True)})
    for identifier in sorted(table_pairs):
        pair = {row["locale"]: row for row in table_rows if row["table_id"] == identifier}
        if set(pair) != {"en", "pt_BR"}:
            findings.append({"asset_id": identifier, "category": "table_locale_pair", "detail": ";".join(sorted(pair))})
            continue
        for locale, row in pair.items():
            for field in ["latex", "tsv", "markdown"]:
                if not (ROOT / row[field]).is_file():
                    findings.append({"asset_id": f"{identifier}:{locale}", "category": "missing_table", "detail": field})
        english_tsv = ReadTsv(ROOT / pair["en"]["tsv"])
        portuguese_tsv = ReadTsv(ROOT / pair["pt_BR"]["tsv"])
        if len(english_tsv) != len(portuguese_tsv):
            findings.append({"asset_id": identifier, "category": "table_row_parity", "detail": f"{len(english_tsv)}:{len(portuguese_tsv)}"})
    captions_en = ReadTsv(ROOT / "figures" / "captions" / "captions_en.tsv")
    captions_pt = ReadTsv(ROOT / "figures" / "captions" / "captions_pt_BR.tsv")
    alt_en = ReadTsv(ROOT / "figures" / "alt_text" / "alt_text_en.tsv")
    alt_pt = ReadTsv(ROOT / "figures" / "alt_text" / "alt_text_pt_BR.tsv")
    for name, rows in [("captions_en", captions_en), ("captions_pt_BR", captions_pt), ("alt_text_en", alt_en), ("alt_text_pt_BR", alt_pt)]:
        if len(rows) != 38 or len({row["figure_id"] for row in rows}) != 38 or any(not all(value.strip() for value in row.values()) for row in rows):
            findings.append({"asset_id": name, "category": "metadata_completeness", "detail": str(len(rows))})
    visual_path = ROOT / "figures" / "visual_qa.tsv"
    if not visual_path.is_file():
        findings.append({"asset_id": "figures", "category": "visual_qa", "detail": "visual_qa.tsv is absent"})
    else:
        visual_rows = ReadTsv(visual_path)
        if len(visual_rows) != 76 or any(row.get("status") != "PASS" for row in visual_rows):
            findings.append({"asset_id": "figures", "category": "visual_qa", "detail": f"rows={len(visual_rows)}"})
    WriteTsv(ROOT / "figures" / "figure_build_ledger.tsv", figure_ledger, ["figure_id", "locale", "source_spec", "source_sha256", "png_width_px", "png_height_px", "svg_viewbox", "intended_width_mm", "status"])
    report = {"status": "PASS" if not findings else "FAIL", "figure_manifest_rows": len(figure_rows), "figure_pairs": len(figure_pairs), "figure_renders": sum((ROOT / row[field]).is_file() for row in figure_rows for field in ["svg", "pdf", "png"]), "table_manifest_rows": len(table_rows), "table_pairs": len(table_pairs), "table_artifacts": sum((ROOT / row[field]).is_file() for row in table_rows for field in ["latex", "tsv", "markdown"]), "finding_count": len(findings), "findings": findings}
    WriteJson(ROOT / "verification" / "reports" / "bilingual_asset_validation.json", report)
    return report
