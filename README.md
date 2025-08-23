# Geo-Tagged Photo Taker — Precise Label Format

This build formats the footer to match your sample:
- **Title:** `City, State, Country`
- **Detail:** `House#, SHORT_PLUS_CODE, <Sub-localities...>, City, State PIN, Country`
- **Lat/Long:** `Lat 12.828459° Long 80.047275°`
- **Time:** `dd/mm/yyyy hh:mm AM/PM GMT +HH:MM`

It also embeds full GPS EXIF metadata.

## Run
```
python -m venv .venv
# Windows: .venv\Scripts\activate
# macOS/Linux:
source .venv/bin/activate
pip install -r requirements.txt
python app.py
```
Open http://127.0.0.1:5000 and allow **camera** and **location**.
