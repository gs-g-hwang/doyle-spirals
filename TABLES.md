# Scripts for the tables of papers A, B, C

Each script recomputes a table from the formulas in the paper. Given the path of the paper's `.tex` file, it also checks every printed value.

| Paper, table | Script | Check |
|---|---|---|
| A, Table 1 (resonant members) | `paperA/tables/tables_A.py` | `python tables_A.py path/to/A.tex` |
| A, Table 2 (comparison with Beardon–Dubejko–Stephenson, our side) | `paperA/tables/tables_A.py` | same run. The BDS side is copied from their Table I. |
| B, Table 1 (all eight columns, including deg and lead) | `paperB/tables/table_Bn_algebraic.py` | `python table_Bn_algebraic.py path/to/B.tex` |
| C, Table 1 (B_{k+1}, B*_k, bounds) | `paperC/tables/table_sk.py` | `python table_sk.py path/to/C.tex` |
| C, Table 2 (Prop. 5.1) | `paperC/rigidity-constants/verify_sk.py`, `verify_sk_arb.py` | see the README there |

Without a path, each script only prints the table.

Tested 2026-10-12 with the versions in `requirements.txt`.
