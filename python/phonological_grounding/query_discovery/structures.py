from __future__ import annotations

import copy
import json
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Iterable, Optional, Sequence

from phonological_opacity.fragments.gua import GuaFragment, load_spec as load_shared_spec

from phonological_grounding.query_discovery import gua_licence
ABSENT = "∅"


def load_licence() -> dict:
    return copy.deepcopy(gua_licence.LICENCE)


def phrase_assignment(word_count: int) -> Optional[list[int]]:
    if word_count <= 0:
        return None
    if word_count <= 3:
        return [0] * word_count
    if word_count == 4:
        return [0, 0, 1, 1]
    return None


@dataclass(frozen=True)
class Skeleton:

    words: tuple[tuple[str, ...], ...]
    phrases: tuple[int, ...]
    tones: tuple[Optional[str], ...]

    @property
    def reference(self) -> tuple[str, ...]:
        return tuple(seg for word in self.words for seg in word)

    @property
    def origin_word(self) -> tuple[int, ...]:
        return tuple(w for w, word in enumerate(self.words) for _ in word)

    @property
    def origin_phrase(self) -> tuple[int, ...]:
        return tuple(self.phrases[w] for w in self.origin_word)

    @property
    def size(self) -> int:
        return sum(len(word) for word in self.words)

    def key(self) -> tuple:
        return (self.words, self.phrases, self.tones)

    def spec_record(self, features: dict, default: dict, identifier: str) -> dict:
        return {
            "id": identifier,
            "words": [list(word) for word in self.words],
            "phrases": list(self.phrases),
            "focal": list(focal_origins(self, features, default)),
            "observation": "",
        }


def nuclear(features: dict, default: dict, segment: str) -> bool:
    return bool(features.get(segment, default)["nuclear"])


def present(features: dict, default: dict, segment: str) -> bool:
    return bool(features.get(segment, default)["present"])


def focal_origins(skeleton: Skeleton, features: dict, default: dict) -> tuple[int, ...]:
    starts: list[int] = []
    running = 0
    for word in skeleton.words:
        starts.append(running)
        running += len(word)
    chosen: set[int] = set()
    for left in range(len(skeleton.words) - 1):
        right = left + 1
        if skeleton.phrases[left] != skeleton.phrases[right]:
            continue
        left_nuclei = [starts[left] + i for i, seg in enumerate(skeleton.words[left])
                       if nuclear(features, default, seg)]
        right_nuclei = [starts[right] + i for i, seg in enumerate(skeleton.words[right])
                        if nuclear(features, default, seg)]
        if left_nuclei:
            chosen.add(left_nuclei[-1])
        if right_nuclei:
            chosen.add(right_nuclei[0])
    return tuple(sorted(chosen))


@dataclass(frozen=True)
class State:

    skeleton: Skeleton
    values: tuple[str, ...]

    def __post_init__(self) -> None:
        if len(self.values) != self.skeleton.size:
            raise ValueError("value/origin length mismatch")

    @staticmethod
    def reference_state(skeleton: Skeleton) -> "State":
        return State(skeleton, skeleton.reference)

    def with_values(self, values: Sequence[str]) -> "State":
        return State(self.skeleton, tuple(values))


@lru_cache(maxsize=None)
def gua_context() -> "GuaContext":
    return GuaContext(load_shared_spec(), load_licence())


class GuaContext:

    def __init__(self, shared: dict, licence: dict):
        self.shared = shared
        self.licence = licence
        self.features: dict = shared["features"]
        self.default: dict = shared["default_segment_features"]
        self.alphabet: list[str] = list(shared["alphabet"])
        self.skeletons: dict[str, Skeleton] = {}
        for record in shared["inputs"]:
            tones = licence["tone"]["per_input"][record["id"]]["tones"]
            skeleton = Skeleton(
                words=tuple(tuple(w) for w in record["words"]),
                phrases=tuple(record["phrases"]),
                tones=tuple(tones),
            )
            if skeleton.size != len(tones):
                raise ValueError(f"{record['id']}: tone list length mismatch")
            for q, (seg, tone) in enumerate(zip(skeleton.reference, tones)):
                is_nuc = nuclear(self.features, self.default, seg)
                if is_nuc and tone not in ("H", "L"):
                    raise ValueError(f"{record['id']}: nuclear origin {q} has no tone")
                if (not is_nuc) and tone is not None:
                    raise ValueError(f"{record['id']}: non-nuclear origin {q} has a tone")
            declared = tuple(record["focal"])
            computed = focal_origins(skeleton, self.features, self.default)
            if declared != computed:
                raise ValueError(
                    f"{record['id']}: focal policy gives {computed}, spec declares {declared}")
            self.skeletons[record["id"]] = skeleton
        self._fragment_cache: dict[tuple, GuaFragment] = {}
        self.words_for_frames = {
            w["id"]: (tuple(w["segments"]), tuple(w["tones"]))
            for w in licence["lexical_words_for_frames"]
        }
        for wid, (segs, tones) in self.words_for_frames.items():
            if len(segs) != len(tones):
                raise ValueError(f"{wid}: segment/tone length mismatch")
            for seg, tone in zip(segs, tones):
                is_nuc = nuclear(self.features, self.default, seg)
                if is_nuc != (tone is not None):
                    raise ValueError(f"{wid}: tone/nuclearity mismatch at {seg}")

    def focal(self, skeleton: Skeleton) -> tuple[int, ...]:
        return focal_origins(skeleton, self.features, self.default)

    def is_present(self, segment: str) -> bool:
        return present(self.features, self.default, segment)

    def is_nuclear(self, segment: str) -> bool:
        return nuclear(self.features, self.default, segment)

    def candidates(self, skeleton: Skeleton) -> list[State]:
        focal = self.focal(skeleton)
        reference = list(skeleton.reference)
        out: list[State] = []
        radix = len(self.alphabet)
        total = radix ** len(focal)
        powers = [radix ** i for i in reversed(range(len(focal)))]
        for index in range(total):
            values = list(reference)
            rest = index
            for q, p in zip(focal, powers):
                values[q] = self.alphabet[rest // p]
                rest %= p
            out.append(State(skeleton, tuple(values)))
        return out

    def fragment(self, skeleton: Skeleton, identifier: str = "frame") -> GuaFragment:
        cached = self._fragment_cache.get(skeleton.key())
        if cached is not None:
            return cached
        record = skeleton.spec_record(self.features, self.default, identifier)
        shim = dict(self.shared)
        shim["inputs"] = list(self.shared["inputs"]) + [record]
        fragment = GuaFragment(shim, identifier)
        self._fragment_cache[skeleton.key()] = fragment
        return fragment


class Undefined(Exception):
    pass


def _rebuild(words: list[list[str]], tones: list[list[Optional[str]]],
             values: list[list[str]]) -> Optional[tuple[Skeleton, tuple[str, ...]]]:
    phrases = phrase_assignment(len(words))
    if phrases is None:
        return None
    skeleton = Skeleton(
        words=tuple(tuple(w) for w in words),
        phrases=tuple(phrases),
        tones=tuple(t for word in tones for t in word),
    )
    flat = tuple(v for word in values for v in word)
    return skeleton, flat


def _split_by_word(state: State) -> tuple[list[list[str]], list[list[Optional[str]]], list[list[str]]]:
    words: list[list[str]] = []
    tones: list[list[Optional[str]]] = []
    values: list[list[str]] = []
    cursor = 0
    for word in state.skeleton.words:
        n = len(word)
        words.append(list(word))
        tones.append(list(state.skeleton.tones[cursor:cursor + n]))
        values.append(list(state.values[cursor:cursor + n]))
        cursor += n
    return words, tones, values


def op_isolate_word(ctx: GuaContext, state: State, index: int) -> State:
    words, tones, values = _split_by_word(state)
    if not 0 <= index < len(words):
        raise Undefined("word index out of range")
    built = _rebuild([words[index]], [tones[index]], [values[index]])
    if built is None:
        raise Undefined("no phrasing")
    return State(built[0], built[1])


def op_drop_word(ctx: GuaContext, state: State, index: int) -> State:
    words, tones, values = _split_by_word(state)
    if not 0 <= index < len(words) or len(words) <= 1:
        raise Undefined("cannot drop")
    keep = [i for i in range(len(words)) if i != index]
    built = _rebuild([words[i] for i in keep], [tones[i] for i in keep],
                     [values[i] for i in keep])
    if built is None:
        raise Undefined("no phrasing")
    return State(built[0], built[1])


def op_prefix_word(ctx: GuaContext, state: State, word_id: str) -> State:
    segs, wtones = ctx.words_for_frames[word_id]
    words, tones, values = _split_by_word(state)
    built = _rebuild([list(segs)] + words, [list(wtones)] + tones,
                     [list(segs)] + values)
    if built is None:
        raise Undefined("no phrasing for this length")
    return State(built[0], built[1])


def op_suffix_word(ctx: GuaContext, state: State, word_id: str) -> State:
    segs, wtones = ctx.words_for_frames[word_id]
    words, tones, values = _split_by_word(state)
    built = _rebuild(words + [list(segs)], tones + [list(wtones)],
                     values + [list(segs)])
    if built is None:
        raise Undefined("no phrasing for this length")
    return State(built[0], built[1])


def op_insert_word_at(ctx: GuaContext, state: State, index: int, word_id: str) -> State:
    segs, wtones = ctx.words_for_frames[word_id]
    words, tones, values = _split_by_word(state)
    if not 0 <= index <= len(words):
        raise Undefined("insertion index out of range")
    built = _rebuild(words[:index] + [list(segs)] + words[index:],
                     tones[:index] + [list(wtones)] + tones[index:],
                     values[:index] + [list(segs)] + values[index:])
    if built is None:
        raise Undefined("no phrasing for this length")
    return State(built[0], built[1])


def op_substitute_word(ctx: GuaContext, state: State, index: int, word_id: str) -> State:
    segs, wtones = ctx.words_for_frames[word_id]
    if segs and segs[0] in ("u", "ʊ"):
        raise Undefined("word-initial high back vowel is unattested")
    words, tones, values = _split_by_word(state)
    if not 0 <= index < len(words):
        raise Undefined("word index out of range")
    words[index] = list(segs)
    tones[index] = list(wtones)
    values[index] = list(segs)
    built = _rebuild(words, tones, values)
    if built is None:
        raise Undefined("no phrasing")
    return State(built[0], built[1])


def op_project_phrase(ctx: GuaContext, state: State, phrase: int) -> State:
    words, tones, values = _split_by_word(state)
    keep = [i for i, p in enumerate(state.skeleton.phrases) if p == phrase]
    if not keep:
        raise Undefined("empty phrase")
    built = _rebuild([words[i] for i in keep], [tones[i] for i in keep],
                     [values[i] for i in keep])
    if built is None:
        raise Undefined("no phrasing")
    return State(built[0], built[1])


def op_rephrase_by_length(ctx: GuaContext, state: State) -> State:
    words, tones, values = _split_by_word(state)
    built = _rebuild(words, tones, values)
    if built is None:
        raise Undefined("no phrasing for this length")
    return State(built[0], built[1])


OPERATION_TABLE = {
    "isolate_word": op_isolate_word,
    "drop_word": op_drop_word,
    "prefix_word": op_prefix_word,
    "suffix_word": op_suffix_word,
    "insert_word_at": op_insert_word_at,
    "substitute_word": op_substitute_word,
    "project_phrase": op_project_phrase,
    "rephrase_by_length": op_rephrase_by_length,
}
