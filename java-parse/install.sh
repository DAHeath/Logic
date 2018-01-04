#!/bin/bash
cp main.byte /usr/local/bin/parse-java-x
cat main.sh | sed 's/main.byte/parse-java-x/' > /usr/local/bin/parse-java
