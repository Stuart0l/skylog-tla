# SkyLog §4.3 TLA+ model

This repository model-checks SkyLog data-path (Appender and Consumer) and reconfiguration
protocols from paper *SkyLog: Reducing Cost and Latency in a Multi-Cloud Shared Log*.

`SkyLogDataPath.tla` covers the normal scenario data path, including appender and
consumer behavior on a stable configuration consists of a home and a mirror, especially
how mirror consumer delivers data. It also covers how order-replicator replicates
metadata. 

`SkyLogHomeUnchanged.tla` covers the reconfiguration protocol when we `dup` the home log
to produce a new mirror log. It contains how the controller initiates the reconfiguration
and coordinates with appenders, as well as how appenders react to controller's controll
message.

`SkyLogHomeChanged.tla` covers the reconfiguration protocol when we move the home log to
a new cloud using the *dup-then-switch* method. It contains the controller and appender
procedures during the reconfiguration, as well as the consumer protocol on how to read across
the switch boundary.

## Files

- `DataPath.cfg`, `HomeUnchanged.cfg`, and `HomeChanged.cfg`: the exhaustive
  finite TLC configurations for those three models.
- `DataPathLiveness.cfg`: ensures once a record is durable at home, the order-replicator
eventually replicates its metadata and the mirror consumer eventually delivers that record.

## Run TLC

Install the official TLA+ tools and point `TLA_TOOLS_JAR` at `tla2tools.jar`.
Java 17 or later is required.

```sh
export TLA_TOOLS_JAR=/absolute/path/to/tla2tools.jar
./run-checks.sh
```

To run an individual check:

```sh
java -cp "$TLA_TOOLS_JAR" tlc2.TLC -workers auto -config HomeChanged.cfg SkyLogHomeChanged.tla
```
