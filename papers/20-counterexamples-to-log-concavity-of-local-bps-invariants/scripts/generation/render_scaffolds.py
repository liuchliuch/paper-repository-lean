#!/usr/bin/env python3
"""Restore pinned current proof scaffolding around freshly generated numeric RHSs.

This module is a text renderer, not a theorem prover. It executes no Lean, Lake,
Comparator or arbitrary code from a template. The shared preparation dispatcher
must check the final SHA-256 and byte size of EVERY output before installing it.
"""
from pathlib import Path
import bisect
import json
import re

TOP = re.compile(r"^(?:noncomputable\s+)?(?:def|theorem|end)\b", re.M)
DEF = re.compile(r"^(?:noncomputable\s+)?def\s+(\w+)[^\n]*?:=", re.M)
MARKER = re.compile(r"@@GENERATED_RHS:(\w+)@@")


def definition_values(text):
    starts = [match.start() for match in TOP.finditer(text)]
    result = {}
    for match in DEF.finditer(text):
        index = bisect.bisect_right(starts, match.start())
        end = starts[index] if index < len(starts) else len(text)
        name = match.group(1)
        if name in result:
            raise ValueError("Duplicate generated definition: " + name)
        result[name] = text[match.end():end].strip()
    return result


def negative_format(value, style):
    if style == "none":
        return value
    # Historic files use three equivalent literal spellings. Preserve the
    # reviewed spelling without altering positive integers or identifiers.
    value = re.sub(r"\(Int.negSucc (\d+)\)",
                   lambda m: "@@NEG:" + str(int(m.group(1)) + 1) + "@@", value)
    value = re.sub(r"\(-(\d+)\)", lambda m: "@@NEG:" + m.group(1) + "@@", value)
    value = re.sub(r"(?<![\w])-(\d+)", lambda m: "@@NEG:" + m.group(1) + "@@", value)
    def render(match):
        number = int(match.group(1))
        if style == "int_neg_succ":
            if number <= 0:
                raise ValueError("Invalid negative literal")
            return "(Int.negSucc " + str(number - 1) + ")"
        if style == "parenthesized":
            return "(-" + str(number) + ")"
        if style == "bare":
            return "-" + str(number)
        raise ValueError("Unknown negative spelling: " + style)
    return re.sub(r"@@NEG:(\d+)@@", render, value)


def restore_scaffolds(project):
    index = json.loads((project / "scripts/generation/template-index.json").read_text())
    for relative, entry in index.items():
        target = project / relative
        # Even proof-only templates require the exporter to create its candidate.
        if not target.is_file():
            raise ValueError("Exporter did not create declared candidate: " + relative)
        values = definition_values(target.read_text())
        template = (project / entry["template"]).read_text()
        expected = entry["replacements"]
        if set(MARKER.findall(template)) != set(expected):
            raise ValueError("Template/index mismatch: " + relative)
        def replace(match):
            name = match.group(1)
            if name not in values:
                raise ValueError("Missing regenerated RHS " + relative + ":" + name)
            return negative_format(values[name], expected[name])
        result = MARKER.sub(replace, template)
        if "@@GENERATED_RHS:" in result:
            raise ValueError("Unfilled template marker: " + relative)
        target.write_text(result)
