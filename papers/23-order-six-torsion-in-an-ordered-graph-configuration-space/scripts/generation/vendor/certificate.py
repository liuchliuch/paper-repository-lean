# Complete construction and verification of the order-six torsion certificate.
# Faithful reconstruction of the paper listing (Appendix A). Python 3.9+.
# No input files or third-party modules.
import argparse
import functools
import hashlib
import inspect
import heapq
import itertools
import json
import math
import pickle
from pathlib import Path
from collections import deque
from types import SimpleNamespace


class SymmetricGroup:

    def __init__(self, n):
        self.n = n
        self.permutations = list(itertools.permutations(range(n)))
        self.index = {p: i for i, p in enumerate(self.permutations)}
        self.identity = self.index[tuple(range(n))]
        self.inverses = []
        for p in self.permutations:
            inverse = [0] * n
            for i, j in enumerate(p):
                inverse[j] = i
            self.inverses.append(self.index[tuple(inverse)])
        self.multiply = functools.lru_cache(maxsize=1000000)(self._multiply)

    def _multiply(self, a, b):
        p, q = (self.permutations[a], self.permutations[b])
        return self.index[tuple((p[i] for i in q))]

    def add_product(self, destination, left, right, sign=1):
        for g, a in left.items():
            for h, b in right.items():
                k = self.multiply(g, h)
                new = destination.get(k, 0) + sign * a * b
                if new:
                    destination[k] = new
                else:
                    destination.pop(k, None)


def is_unit(value):
    return len(value) == 1 and abs(next(iter(value.values()))) == 1


class GroupRingMatrix:

    def __init__(self, group, nrows, columns):
        self.group = group
        self.rows = [{} for _ in range(nrows)]
        self.cols = columns
        for j, col in enumerate(columns):
            for i, a in col.items():
                assert a
                self.rows[i][j] = a

    def unit_reduce(self, on_pivot=None):
        rv = [0] * len(self.rows)
        cv = [0] * len(self.cols)
        rh = [(len(row), i, 0) for i, row in enumerate(self.rows) if row]
        ch = [(len(col), j, 0) for j, col in enumerate(self.cols) if col]
        heapq.heapify(rh)
        heapq.heapify(ch)
        count = 0

        def candidate(heap, vectors, versions, opposite):
            while heap:
                _, index, version = heap[0]
                if version != versions[index] or not vectors[index]:
                    heapq.heappop(heap)
                    continue
                units = [k for k, a in vectors[index].items() if is_unit(a)]
                if not units:
                    heapq.heappop(heap)
                    continue
                k = min(units, key=lambda t: (len(opposite[t]), t))
                cost = (len(vectors[index]) - 1) * (len(opposite[k]) - 1)
                return (cost, index, k)
            return None

        while True:
            rc = candidate(rh, self.rows, rv, self.cols)
            cc = candidate(ch, self.cols, cv, self.rows)
            if rc is None and cc is None:
                break
            if cc is None or (rc is not None and rc[0] <= cc[0]):
                _, r, c = rc
            else:
                _, c, r = cc
            unit = self.rows[r][c]
            g, sign = next(iter(unit.items()))
            assert abs(sign) == 1
            inverse = self.group.inverses[g]
            prow = list(self.rows[r].items())
            pcol = list(self.cols[c].items())
            if on_pivot:
                on_pivot(r, c, unit)
            for j, b in prow:
                if j == c:
                    continue
                factor = {
                    self.group.multiply(h, inverse): sign * coefficient
                    for h, coefficient in b.items()
                }
                col = self.cols[j]
                del col[r]
                for i, x in pcol:
                    if i == r:
                        continue
                    new = col.get(i, {}).copy()
                    self.group.add_product(new, factor, x, sign=-1)
                    if new:
                        col[i] = new
                        self.rows[i][j] = new
                    else:
                        col.pop(i, None)
                        self.rows[i].pop(j, None)
            for i, _ in pcol:
                self.rows[i].pop(c, None)
            self.rows[r] = {}
            self.cols[c] = {}
            for i, _ in pcol:
                rv[i] += 1
                if self.rows[i]:
                    heapq.heappush(rh, (len(self.rows[i]), i, rv[i]))
            for j, _ in prow:
                cv[j] += 1
                if self.rows[j]:
                    heapq.heappush(ch, (len(self.cols[j]), j, cv[j]))
            count += 1
            if len(rh) > max(10000, 4 * len(self.rows)):
                rh = [(len(row), i, rv[i]) for i, row in enumerate(self.rows) if row]
                heapq.heapify(rh)
            if len(ch) > max(10000, 4 * len(self.cols)):
                ch = [(len(col), j, cv[j]) for j, col in enumerate(self.cols) if col]
                heapq.heapify(ch)
        return count


class SparseMatrix:

    def __init__(self, nrows: int, columns: list):
        self.rows = [{} for _ in range(nrows)]
        self.cols = columns
        for j, col in enumerate(columns):
            for i, a in col.items():
                if not a:
                    raise ValueError("Explicit zero entry")
                self.rows[i][j] = a

    def unit_reduce(self, on_pivot=None):
        """Schur-complement cancellation at unit pivots; exact over Z."""
        rversions = [0] * len(self.rows)
        cversions = [0] * len(self.cols)
        rh = [(len(row), i, 0) for i, row in enumerate(self.rows) if row]
        ch = [(len(col), j, 0) for j, col in enumerate(self.cols) if col]
        heapq.heapify(rh)
        heapq.heapify(ch)
        rank = 0

        def candidate(heap, vectors, versions, opposite):
            while heap:
                _, idx, version = heap[0]
                if version != versions[idx] or not vectors[idx]:
                    heapq.heappop(heap)
                    continue
                unit = [k for k, a in vectors[idx].items() if abs(a) == 1]
                if not unit:
                    heapq.heappop(heap)
                    continue
                k = min(unit, key=lambda x: (len(opposite[x]), x))
                cost = (len(vectors[idx]) - 1) * (len(opposite[k]) - 1)
                return (cost, idx, k)
            return None

        while True:
            rc = candidate(rh, self.rows, rversions, self.cols)
            cc = candidate(ch, self.cols, cversions, self.rows)
            if rc is None and cc is None:
                break
            if cc is None or (rc is not None and rc[0] <= cc[0]):
                _, r, c = rc
            else:
                _, c, r = cc
            a = self.rows[r][c]
            assert abs(a) == 1
            prow = list(self.rows[r].items())
            pcol = list(self.cols[c].items())
            touched_rows = {i for i, _ in pcol}
            touched_cols = {j for j, _ in prow}
            if on_pivot is not None:
                on_pivot(r, c, a)
            for j, b in prow:
                if j == c:
                    continue
                factor = a * b
                col = self.cols[j]
                del col[r]
                for i, x in pcol:
                    if i == r:
                        continue
                    val = col.get(i, 0) - factor * x
                    if val:
                        col[i] = val
                        self.rows[i][j] = val
                    else:
                        col.pop(i, None)
                        self.rows[i].pop(j, None)
            for i, _ in pcol:
                self.rows[i].pop(c, None)
            self.rows[r] = {}
            self.cols[c] = {}
            for i in touched_rows:
                rversions[i] += 1
                if self.rows[i]:
                    heapq.heappush(rh, (len(self.rows[i]), i, rversions[i]))
            for j in touched_cols:
                cversions[j] += 1
                if self.cols[j]:
                    heapq.heappush(ch, (len(self.cols[j]), j, cversions[j]))
            rank += 1
            if len(rh) > max(10000, 4 * len(self.rows)):
                rh = [(len(row), i, rversions[i]) for i, row in enumerate(self.rows) if row]
                heapq.heapify(rh)
            if len(ch) > max(10000, 4 * len(self.cols)):
                ch = [(len(col), j, cversions[j]) for j, col in enumerate(self.cols) if col]
                heapq.heapify(ch)
        return rank


def core_edges():
    return (
        [(0, 1)] * 3
        + [(0, 2), (0, 3), (1, 4), (1, 5)]
        + list(itertools.combinations(range(2, 6), 2))
    )


class EquivariantAbrams:

    def __init__(self):
        n = 4
        core = core_edges()
        edges = []
        for e, (u, v) in enumerate(core):
            x, y = (6 + 2 * e, 7 + 2 * e)
            edges.extend([(u, x), (x, y), (y, v)])
        self.graph = SimpleNamespace(vertices=32, edges=edges)
        self.n = n
        self.group = SymmetricGroup(n)
        self.cells = []
        self.lookup = []
        vertices = self.graph.vertices
        for q in range(n + 1):
            cells = []
            for edgeids in itertools.combinations(range(len(self.graph.edges)), q):
                occupied = set()
                valid = True
                for edge in edgeids:
                    endpoints = set(self.graph.edges[edge])
                    if occupied & endpoints:
                        valid = False
                        break
                    occupied.update(endpoints)
                if not valid:
                    continue
                free = [v for v in range(vertices) if v not in occupied]
                for stationary in itertools.combinations(free, n - q):
                    cells.append(stationary + tuple((vertices + e for e in edgeids)))
            cells.sort()
            self.cells.append(cells)
            self.lookup.append({cell: i for i, cell in enumerate(cells)})
        self.boundaries = {}

    def build_boundaries(self):
        vertices = self.graph.vertices
        for q in [3]:
            columns = []
            for cell in self.cells[q]:
                col = {}
                for k, token in enumerate(cell):
                    if token < vertices:
                        continue
                    edge_position = k - (self.n - q)
                    for endpoint, factor in zip(
                        self.graph.edges[token - vertices], (-1, 1)
                    ):
                        face = list(cell)
                        face[k] = endpoint
                        permutation = tuple(
                            sorted(range(self.n), key=lambda i: face[i])
                        )
                        target = tuple((face[i] for i in permutation))
                        target_index = self.lookup[q - 1][target]
                        g = self.group.index[permutation]
                        value = factor * (-1) ** edge_position
                        entry = col.setdefault(target_index, {})
                        entry[g] = entry.get(g, 0) + value
                        if not entry[g]:
                            del entry[g]
                if not entry:
                    del col[target_index]
                # keep empty columns allowed (all-zero column)
                columns.append(col)
            self.boundaries[q] = GroupRingMatrix(
                self.group, len(self.cells[q - 1]), columns
            )


def bezout_vector(values):
    """Return g>=0 and coefficients with sum(values[i]*coefficients[i])=g."""
    coefficients = {}
    gcd = 0
    for key, value in values.items():
        if not value:
            continue
        old_r, r = (gcd, value)
        old_s, s = (1, 0)
        old_t, t = (0, 1)
        while r:
            quotient = old_r // r
            old_r, r = (r, old_r - quotient * r)
            old_s, s = (s, old_s - quotient * s)
            old_t, t = (t, old_t - quotient * t)
        if old_r < 0:
            old_r, old_s, old_t = (-old_r, -old_s, -old_t)
        coefficients = {i: a * old_s for i, a in coefficients.items() if a * old_s}
        if old_t:
            coefficients[key] = coefficients.get(key, 0) + old_t
        gcd = old_r
        if gcd == 1:
            break
    assert sum((values[i] * a for i, a in coefficients.items())) == gcd
    return (gcd, coefficients)


def integer_certificate(matrix):
    records = []

    def pivot(r, c, a):
        records.append(
            (
                r,
                c,
                a,
                tuple(((j, b) for j, b in matrix.rows[r].items() if j != c)),
                tuple(((i, x) for i, x in matrix.cols[c].items() if i != r)),
            )
        )

    pivots = matrix.unit_reduce(on_pivot=pivot)
    nonzero = {j: col for j, col in enumerate(matrix.cols) if col}
    assert nonzero
    first = next(iter(nonzero.values()))
    divisor = math.gcd(*first.values())
    z = {i: a // divisor for i, a in first.items()}
    gcd, functional = bezout_vector(z)
    assert gcd == 1
    scalars = {}
    for j, col in nonzero.items():
        scalar = sum((a * col.get(i, 0) for i, a in functional.items()))
        assert col == {i: scalar * a for i, a in z.items() if scalar * a}
        scalars[j] = scalar
    order, source = bezout_vector(scalars)
    assert order == 6
    phi = {i: a % order for i, a in functional.items() if a % order}
    for r, c, a, prow, pcol in reversed(records):
        coefficient = -a * sum((b * source.get(j, 0) for j, b in prow))
        if coefficient:
            source[c] = coefficient
        value = -a * sum((x * phi.get(i, 0) for i, x in pcol)) % order
        if value:
            phi[r] = value
    return (z, source, phi, pivots)


def reduction_fingerprint():
    """Fingerprint only the graph, cell enumeration and reduction algorithms."""
    pieces = [inspect.getsource(obj) for obj in (SymmetricGroup, GroupRingMatrix, core_edges, EquivariantAbrams)]
    return hashlib.sha256("\n".join(pieces).encode()).hexdigest()


def construct(strict_source_counts=True, checkpoint=None):
    model = EquivariantAbrams()
    model.build_boundaries()
    matrix = model.boundaries[3]
    records = []

    def pivot(r, c, unit):
        g, sign = next(iter(unit.items()))
        records.append(
            (
                r,
                c,
                g,
                sign,
                tuple(((j, a) for j, a in matrix.rows[r].items() if j != c)),
                tuple(((i, a) for i, a in matrix.cols[c].items() if i != r)),
            )
        )

    checkpoint = Path(checkpoint) if checkpoint else None
    fingerprint = reduction_fingerprint()
    if checkpoint and checkpoint.exists():
        with checkpoint.open("rb") as stream:
            saved_fingerprint, gpivots, nrows, columns, records = pickle.load(stream)
        if saved_fingerprint != fingerprint:
            raise ValueError("Checkpoint algorithm fingerprint mismatch; use a fresh checkpoint path")
        matrix = GroupRingMatrix(model.group, nrows, columns)
        print("Restored group-ring checkpoint", gpivots, flush=True)
    else:
        gpivots = matrix.unit_reduce(on_pivot=pivot)
        if checkpoint:
            with checkpoint.open("wb") as stream:
                pickle.dump((fingerprint, gpivots, len(matrix.rows), matrix.cols, records), stream)
            print("Saved group-ring checkpoint", gpivots, flush=True)
    rowids = [i for i, row in enumerate(matrix.rows) if row]
    colids = [j for j, col in enumerate(matrix.cols) if col]
    assert gpivots == 131107
    print("Group-ring residual", len(rowids), len(colids), "cells", list(map(len, model.cells)), flush=True)
    if strict_source_counts:
        assert (len(rowids), len(colids)) == (3361, 61), (len(rowids), len(colids))
    rindex = {r: i for i, r in enumerate(rowids)}
    group = model.group
    N = len(group.permutations)
    multiplication = [[group.multiply(g, h) for h in range(N)] for g in range(N)]
    right_shifts = [[multiplication[g][h] for g in range(N)] for h in range(N)]
    columns = []
    for c in colids:
        for g in range(N):
            col = {}
            for r, a in matrix.cols[c].items():
                offset = rindex[r] * N
                for h, value in a.items():
                    col[offset + multiplication[g][h]] = value
            columns.append(col)
    integer = SparseMatrix(len(rowids) * N, columns)
    z, source, phi, ipivots = integer_certificate(integer)
    assert ipivots == 118
    del integer
    zgroup = {}
    for i, a in z.items():
        r, g = divmod(i, N)
        zgroup.setdefault(rowids[r], {})[g] = a
    bgroup = {}
    for j, a in source.items():
        c, g = divmod(j, N)
        bgroup.setdefault(colids[c], {})[g] = a
    phigroup = {}
    for i, a in phi.items():
        r, g = divmod(i, N)
        phigroup.setdefault(rowids[r], [0] * N)[g] = a
    for r, c, g, sign, prow, pcol in reversed(records):
        inverse = group.inverses[g]
        coefficient = {}
        for j, a in prow:
            value = bgroup.get(j)
            if value:
                group.add_product(coefficient, value, a)
        if coefficient:
            bgroup[c] = {
                multiplication[h][inverse]: -sign * a for h, a in coefficient.items()
            }
        values = [0] * N
        for i, a in pcol:
            functional = phigroup.get(i)
            if functional is None:
                continue
            for h, coefficient_a in a.items():
                factor = -sign * coefficient_a
                if factor % 6 == 0:
                    continue
                shift = right_shifts[multiplication[inverse][h]]
                for u in range(N):
                    values[u] += factor * functional[shift[u]]
        values = [x % 6 for x in values]
        if any(values):
            phigroup[r] = values
    del records
    result = {
        "modulus": 6,
        "particle_count": 4,
        "core_graph": {
            "vertices": 6,
            "oriented_edges": [list(e) for e in core_edges()],
        },
        "subdivided_graph": {
            "vertices": model.graph.vertices,
            "oriented_edges": model.graph.edges,
        },
        "permutations": [list(p) for p in group.permutations],
        "unlabelled_cell_counts": list(map(len, model.cells)),
        "cycle_z": [
            [list(model.cells[2][r]), sorted(a.items())]
            for r, a in sorted(zgroup.items())
        ],
        "bounding_chain_b": [
            [list(model.cells[3][c]), sorted(a.items())]
            for c, a in sorted(bgroup.items())
        ],
        "detecting_cocycle_phi": [
            [list(model.cells[2][r]), a] for r, a in sorted(phigroup.items())
        ],
        "construction": {
            "group_ring_unit_pivots": gpivots,
            "integer_unit_pivots": ipivots,
            "group_ring_nonzero_residual_rows": len(rowids),
            "group_ring_nonzero_residual_columns": len(colids),
            "reduction_algorithm_sha256": fingerprint,
        },
    }
    return result


def check(certificate, strict_source_counts=True):
    if not __debug__:
        raise RuntimeError(
            "Run this verifier without -O; its assertions are the certificate checks."
        )
    assert certificate["particle_count"] == 4
    assert certificate["modulus"] == 6
    core = (
        [(0, 1)] * 3
        + [(0, 2), (0, 3), (1, 4), (1, 5)]
        + list(itertools.combinations(range(2, 6), 2))
    )
    assert certificate["core_graph"] == {
        "vertices": 6,
        "oriented_edges": [list(e) for e in core],
    }
    expected_edges = []
    for e, (u, v) in enumerate(core):
        x, y = (6 + 2 * e, 7 + 2 * e)
        expected_edges.extend([(u, x), (x, y), (y, v)])
    graph = certificate["subdivided_graph"]
    vertices = graph["vertices"]
    edges = [tuple(e) for e in graph["oriented_edges"]]
    assert vertices == 32 and edges == expected_edges and (len(edges) == 39)
    adjacency = [[] for _ in range(vertices)]
    for e, (u, v) in enumerate(edges):
        adjacency[u].append((v, e))
        adjacency[v].append((u, e))

    def distances(start, omitted_edge=None):
        distance = {start: 0}
        queue = deque([start])
        while queue:
            u = queue.popleft()
            for v, e in adjacency[u]:
                if e != omitted_edge and v not in distance:
                    distance[v] = distance[u] + 1
                    queue.append(v)
        return distance

    assert len(distances(0)) == vertices
    special = [v for v in range(vertices) if len(adjacency[v]) != 2]
    assert special == list(range(6))
    shortest_special_path = min(
        (distances(u)[v] for u, v in itertools.combinations(special, 2))
    )
    girth = min((distances(u, e).get(v, 10**9) + 1 for e, (u, v) in enumerate(edges)))
    assert shortest_special_path >= 3 and girth >= 5
    permutations = list(itertools.permutations(range(4)))
    assert certificate["permutations"] == [list(p) for p in permutations]
    pindex = {p: i for i, p in enumerate(permutations)}
    multiply = [
        [pindex[tuple((p[q[i]] for i in range(4)))] for q in permutations]
        for p in permutations
    ]
    zero = (0,) * 24

    def validate_cell(cell, dimension):
        assert len(cell) == 4 and all((type(x) is int for x in cell))
        assert tuple(sorted(cell)) == cell and len(set(cell)) == 4
        assert sum((x >= vertices for x in cell)) == dimension
        occupied = 0
        for token in cell:
            assert 0 <= token < vertices + len(edges)
            if token < vertices:
                closure = 1 << token
            else:
                u, v = edges[token - vertices]
                closure = 1 << u | 1 << v
            assert not occupied & closure, ("intersecting cell closures", cell)
            occupied |= closure

    def read_chain(name, dimension):
        chain = {}
        for cell, entries in certificate[name]:
            cell = tuple(cell)
            validate_cell(cell, dimension)
            assert cell not in chain
            values = [0] * 24
            for p, a in entries:
                assert type(p) is int and 0 <= p < 24
                assert type(a) is int and a != 0 and (values[p] == 0)
                values[p] = a
            assert any(values)
            chain[cell] = values
        return chain

    z = read_chain("cycle_z", 2)
    if strict_source_counts:
        assert len(z) == 409
    signs = [
        (-1) ** sum(p[i] > p[j] for i in range(4) for j in range(i + 1, 4))
        for p in permutations
    ]
    alternating_form = all(
        values[0] in (-1, 1) and values == [values[0] * a for a in signs]
        for values in z.values()
    )
    if strict_source_counts:
        assert alternating_form
    b = read_chain("bounding_chain_b", 3)
    phi = {}
    for cell, values in certificate["detecting_cocycle_phi"]:
        cell = tuple(cell)
        validate_cell(cell, 2)
        assert cell not in phi and len(values) == 24
        assert all((type(x) is int and 0 <= x < 6 for x in values)) and any(values)
        phi[cell] = values

    def faces(cell):
        """Boundary of the canonical oriented cube, with its label maps."""
        axis = 0
        for coordinate, token in enumerate(cell):
            if token < vertices:
                continue
            for endpoint, end_sign in zip(edges[token - vertices], (-1, 1)):
                ordered_face = list(cell)
                ordered_face[coordinate] = endpoint
                old_coordinates = tuple(
                    sorted(range(4), key=lambda i: ordered_face[i])
                )
                canonical_face = tuple((ordered_face[i] for i in old_coordinates))
                yield (
                    canonical_face,
                    pindex[old_coordinates],
                    end_sign * (-1) ** axis,
                )
            axis += 1

    def boundary(chain):
        answer = {}
        for cell, coefficients in chain.items():
            support = [(p, a) for p, a in enumerate(coefficients) if a]
            for face, q, sign in faces(cell):
                row = answer.setdefault(face, [0] * 24)
                for p, a in support:
                    row[multiply[p][q]] += sign * a
        return {cell: values for cell, values in answer.items() if any(values)}

    assert not boundary(z), "The proposed 2-chain is not a cycle."
    expected_boundary = {cell: [6 * a for a in values] for cell, values in z.items()}
    assert (
        boundary(b) == expected_boundary
    ), "The displayed 3-chain does not bound 6*z."
    evaluation = (
        sum(
            (
                a * phi.get(cell, zero)[p]
                for cell, values in z.items()
                for p, a in enumerate(values)
            )
        )
        % 6
    )
    assert evaluation == 1, (
        "The cocycle does not detect z with value 1.",
        evaluation,
    )
    unlabelled_cubes = 0
    for edge_ids in itertools.combinations(range(len(edges)), 3):
        endpoints = [v for e in edge_ids for v in edges[e]]
        if len(set(endpoints)) != 6:
            continue
        occupied = set(endpoints)
        edge_tokens = tuple((vertices + e for e in edge_ids))
        for stationary in range(vertices):
            if stationary in occupied:
                continue
            cell = (stationary,) + edge_tokens
            evaluations = [0] * 24
            for face, q, sign in faces(cell):
                values = phi.get(face)
                if values is None:
                    continue
                for p in range(24):
                    evaluations[p] += sign * values[multiply[p][q]]
            assert all((value % 6 == 0 for value in evaluations)), (
                "Cocycle condition fails at",
                cell,
                evaluations,
            )
            unlabelled_cubes += 1
    assert unlabelled_cubes == 174772
    assert certificate["unlabelled_cell_counts"][3] == unlabelled_cubes
    return {
        "integer_and_mod_six_identities_verified": True,
        "lean_kernel_verified": False,
        "topological_transfer_verified": False,
        "source_alternating_form_reproduced": alternating_form,
        "cycle_canonical_support": len(z),
        "subdivided_graph_vertices": vertices,
        "subdivided_graph_edges": len(edges),
        "shortest_path_between_special_vertices": shortest_special_path,
        "girth": girth,
        "labelled_3_cubes_checked": 24 * unlabelled_cubes,
        "cycle_nonzero_coefficients": sum(
            (sum((bool(a) for a in values)) for values in z.values())
        ),
        "bounding_chain_nonzero_coefficients": sum(
            (sum((bool(a) for a in values)) for values in b.values())
        ),
        "cocycle_nonzero_values": sum(
            (sum((bool(a) for a in values)) for values in phi.values())
        ),
        "cocycle_evaluation_on_z_mod_6": evaluation,
    }


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O: assertions must be enabled.")
    parser = argparse.ArgumentParser(description="External exact certificate construction/checking; not a Lean proof")
    parser.add_argument("--check", type=Path, help="Verify an existing certificate without reduction")
    parser.add_argument("--output", type=Path, default=Path("work/certificate-data.json"))
    parser.add_argument("--report", type=Path, default=Path("work/certificate-verification.json"))
    parser.add_argument("--checkpoint", type=Path, help="Local reduction cache, checked against algorithm fingerprint")
    parser.add_argument("--allow-alternative", action="store_true", help="Verify the four identities even when source-specific support counts differ")
    args = parser.parse_args()
    strict = not args.allow_alternative
    if args.check:
        certificate = json.loads(args.check.read_text())
    else:
        certificate = construct(strict_source_counts=strict, checkpoint=args.checkpoint)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(certificate) + "\n")
    result = check(certificate, strict_source_counts=strict)
    actual_counts = (result["cycle_nonzero_coefficients"], result["bounding_chain_nonzero_coefficients"], result["cocycle_nonzero_values"])
    source_counts = (9816, 236992, 214457)
    result["source_support_counts_reproduced"] = actual_counts == source_counts
    result["source_expected_support_counts"] = list(source_counts)
    if strict:
        assert actual_counts == source_counts, actual_counts
    result["construction"] = certificate["construction"]
    result["certificate_sha256"] = hashlib.sha256((args.check or args.output).read_bytes()).hexdigest()
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
