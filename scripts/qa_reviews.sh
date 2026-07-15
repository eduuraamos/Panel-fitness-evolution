#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
PYTHON_BIN="$ROOT_DIR/.venv/bin/python"
SERVER_URL="${SERVER_URL:-http://127.0.0.1:8005}"
CLIENT_ID="${CLIENT_ID:-5}"
REVIEW_DATE_1="${REVIEW_DATE_1:-2026-07-10}"
REVIEW_DATE_2="${REVIEW_DATE_2:-2026-07-15}"
REVIEW_DATE_3="${REVIEW_DATE_3:-2026-07-20}"
DB_PATH="$ROOT_DIR/data/foods.db"

if ! lsof -nP -iTCP:8005 -sTCP:LISTEN >/dev/null 2>&1; then
  echo "No server listening on 8005. Start scripts/serve_foods.py first." >&2
  exit 1
fi

ADMIN_COOKIE="$($PYTHON_BIN - <<'PY' | tail -n 1
import sys
sys.path.insert(0, 'scripts')
import serve_foods as s
print(s.make_admin_portal_session_token(s.get_admin_portal_username()))
PY
)"

CLIENT_COOKIE="$($PYTHON_BIN - <<'PY' | tail -n 1
import sys
sys.path.insert(0, 'scripts')
import serve_foods as s
print(s.make_client_portal_session_token(5))
PY
)"

BASE64_1X1_PNG='data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO8B9WQAAAAASUVORK5CYII='

assert_http_303() {
  local output="$1"
  grep -q '^HTTP/1\.0 303' <<<"$output"
}

echo "[1/6] Save review schedule"
schedule_resp="$(curl -sS -i -X POST "$SERVER_URL/set_client_review_schedule" \
  -H "Cookie: admin_portal_session=$ADMIN_COOKIE" \
  --data "client_id=$CLIENT_ID" \
  --data 'review_schedule_mode=monthly_days' \
  --data 'review_month_days=1,15' \
  --data 'review_weekday=1' \
  --data 'review_custom_interval_days=10' \
  --data 'review_anchor_date=2026-07-15' \
  --data-urlencode "return_to=/client_profile?id=$CLIENT_ID&section=reviews")"
printf '%s\n' "$schedule_resp" | sed -n '1,6p'
assert_http_303 "$schedule_resp"

echo "[2/6] Submit review #1"
review_1_resp="$(curl -sS -i -X POST "$SERVER_URL/submit_client_review" \
  -H "Cookie: client_portal_session=$CLIENT_COOKIE" \
  --data "client_id=$CLIENT_ID" \
  --data "review_date=$REVIEW_DATE_1" \
  --data-urlencode "photo_front_path_data_url=$BASE64_1X1_PNG" \
  --data-urlencode "photo_left_path_data_url=$BASE64_1X1_PNG" \
  --data-urlencode "photo_right_path_data_url=$BASE64_1X1_PNG" \
  --data-urlencode "photo_back_path_data_url=$BASE64_1X1_PNG" \
  --data 'neck_cm=38.0' \
  --data 'waist_navel_cm=88.0' \
  --data 'upper_chest_cm=102.0' \
  --data-urlencode "return_to=/client_app?section=reviews")"
printf '%s\n' "$review_1_resp" | sed -n '1,6p'
assert_http_303 "$review_1_resp"

echo "[3/6] Submit review #2"
review_2_resp="$(curl -sS -i -X POST "$SERVER_URL/submit_client_review" \
  -H "Cookie: client_portal_session=$CLIENT_COOKIE" \
  --data "client_id=$CLIENT_ID" \
  --data "review_date=$REVIEW_DATE_2" \
  --data-urlencode "photo_front_path_data_url=$BASE64_1X1_PNG" \
  --data-urlencode "photo_left_path_data_url=$BASE64_1X1_PNG" \
  --data-urlencode "photo_right_path_data_url=$BASE64_1X1_PNG" \
  --data-urlencode "photo_back_path_data_url=$BASE64_1X1_PNG" \
  --data 'neck_cm=39.0' \
  --data 'waist_navel_cm=86.5' \
  --data 'upper_chest_cm=103.0' \
  --data-urlencode "return_to=/client_app?section=reviews")"
printf '%s\n' "$review_2_resp" | sed -n '1,6p'
assert_http_303 "$review_2_resp"

echo "[4/6] Submit review #3"
review_3_resp="$(curl -sS -i -X POST "$SERVER_URL/submit_client_review" \
  -H "Cookie: client_portal_session=$CLIENT_COOKIE" \
  --data "client_id=$CLIENT_ID" \
  --data "review_date=$REVIEW_DATE_3" \
  --data-urlencode "photo_front_path_data_url=$BASE64_1X1_PNG" \
  --data-urlencode "photo_left_path_data_url=$BASE64_1X1_PNG" \
  --data-urlencode "photo_right_path_data_url=$BASE64_1X1_PNG" \
  --data-urlencode "photo_back_path_data_url=$BASE64_1X1_PNG" \
  --data 'neck_cm=39.5' \
  --data 'waist_navel_cm=86.0' \
  --data 'upper_chest_cm=103.5' \
  --data-urlencode "return_to=/client_app?section=reviews")"
printf '%s\n' "$review_3_resp" | sed -n '1,6p'
assert_http_303 "$review_3_resp"

REVIEW_ID="$(sqlite3 "$DB_PATH" "SELECT id FROM client_reviews WHERE client_id=$CLIENT_ID ORDER BY review_date DESC, id DESC LIMIT 1;")"
if [[ -z "$REVIEW_ID" ]]; then
  echo "Could not resolve latest review_id" >&2
  exit 1
fi

echo "[5/6] Save professional feedback"
feedback_resp="$(curl -sS -i -X POST "$SERVER_URL/save_client_review_feedback" \
  -H "Cookie: admin_portal_session=$ADMIN_COOKIE" \
  --data "client_id=$CLIENT_ID" \
  --data "review_id=$REVIEW_ID" \
  --data-urlencode 'professional_feedback=Buen progreso en cintura y postura. Mantener técnica.' \
  --data-urlencode "return_to=/client_profile?id=$CLIENT_ID&section=reviews")"
printf '%s\n' "$feedback_resp" | sed -n '1,6p'
assert_http_303 "$feedback_resp"

echo "[6/6] Validate rendering and persistence"
calendar_html="$(curl -sS "$SERVER_URL/client_app?section=calendar" -H "Cookie: client_portal_session=$CLIENT_COOKIE")"
reviews_html="$(curl -sS "$SERVER_URL/client_app?section=reviews&review_id=$REVIEW_ID" -H "Cookie: client_portal_session=$CLIENT_COOKIE")"

grep -q 'cal-chip-review' <<<"$calendar_html"
grep -q 'Revision programada' <<<"$calendar_html"
grep -q 'review-compare-wrap' <<<"$reviews_html"
grep -q 'review-measures-table' <<<"$reviews_html"
grep -q 'Buen progreso en cintura y postura' <<<"$reviews_html"

sqlite3 "$DB_PATH" "SELECT COUNT(*) FROM client_reviews WHERE client_id=$CLIENT_ID AND professional_feedback LIKE 'Buen progreso en cintura%';" | grep -q '^1$'

echo "Review QA passed for client_id=$CLIENT_ID."