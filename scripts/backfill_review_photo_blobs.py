#!/usr/bin/env python3
"""Backfill review photos into DB blobs so they remain available across runtimes.

Usage:
  DATABASE_URL=... python scripts/backfill_review_photo_blobs.py
  python scripts/backfill_review_photo_blobs.py
"""

from db_adapter import sqlite3_compat as sqlite3
from serve_foods import DB_PATH, REVIEW_PHOTO_FIELDS, _read_review_photo_from_path, ensure_client_reviews_table


def main():
    ensure_client_reviews_table()

    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()

    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS client_review_photo_blobs (
            review_id INTEGER NOT NULL,
            photo_field TEXT NOT NULL,
            mime_type TEXT NOT NULL,
            photo_blob BYTEA NOT NULL,
            created_at TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            PRIMARY KEY(review_id, photo_field),
            FOREIGN KEY(review_id) REFERENCES client_reviews(id) ON DELETE CASCADE
        )
        """
    )

    select_cols = ", ".join([f"COALESCE({k}, '')" for k, _ in REVIEW_PHOTO_FIELDS])
    cur.execute(f"SELECT id, client_id, {select_cols} FROM client_reviews")
    rows = cur.fetchall()

    recovered = 0
    missing = 0
    scanned = 0
    unresolved = []

    for row in rows:
        review_id = int(row[0])
        client_id = int(row[1] or 0)
        for idx, (field_key, _label) in enumerate(REVIEW_PHOTO_FIELDS, start=2):
            path_text = str(row[idx] or "").strip()
            if not path_text:
                continue
            scanned += 1

            resolved = _read_review_photo_from_path(path_text)
            if not resolved:
                missing += 1
                unresolved.append((client_id, review_id, field_key, path_text))
                continue

            mime_type, body = resolved
            if not body:
                missing += 1
                unresolved.append((client_id, review_id, field_key, path_text))
                continue

            cur.execute(
                """
                INSERT INTO client_review_photo_blobs(review_id, photo_field, mime_type, photo_blob, created_at, updated_at)
                VALUES(?,?,?,?,CURRENT_TIMESTAMP,CURRENT_TIMESTAMP)
                ON CONFLICT(review_id, photo_field)
                DO UPDATE SET
                    mime_type = excluded.mime_type,
                    photo_blob = excluded.photo_blob,
                    updated_at = CURRENT_TIMESTAMP
                """,
                (review_id, field_key, mime_type or "application/octet-stream", body),
            )
            recovered += 1

    conn.commit()

    print(f"reviews_scanned={len(rows)}")
    print(f"photo_slots_with_path={scanned}")
    print(f"recovered_or_refreshed={recovered}")
    print(f"still_missing={missing}")

    if unresolved:
        print("\\nUnresolved photo slots (client_id, review_id, field, path):")
        for client_id, review_id, field_key, path_text in unresolved:
            print(f"{client_id}, {review_id}, {field_key}, {path_text}")

    cur.close()
    conn.close()


if __name__ == "__main__":
    main()
