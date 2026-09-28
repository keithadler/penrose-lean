import Penrose

/-- Writes `Penrose.widgetProps` to `docs/props.json` for the browser version. -/
def main : IO Unit :=
  IO.FS.writeFile "docs/props.json" Penrose.widgetProps.compress
