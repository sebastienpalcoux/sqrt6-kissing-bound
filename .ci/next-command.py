from pathlib import Path

# Stop the bounded development runner. Its existing final step exports the
# current proof candidates and compiler logs as a workflow artifact.
Path('.ci/STOP_DEVELOPMENT_SESSION').touch()
print('Development session stopped. No certification is claimed.')
