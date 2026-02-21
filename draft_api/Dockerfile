FROM python:3.12-slim

WORKDIR /app
COPY draft_api/server.py /app/server.py

ENV DRAFT_DB_HOST=0.0.0.0
ENV DRAFT_DB_PORT=8787
ENV DRAFT_DB_PATH=/data/drafts.sqlite3

EXPOSE 8787

CMD ["python3", "/app/server.py"]
