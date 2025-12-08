# Anti-Join and Set-Difference Patterns – Evidence

This note collects a compact pointer list of docs and papers that show anti-joins / NOT EXISTS / EXCEPT / tombstones are actually implemented and used in these systems, plus where they are not yet fully supported.

⸻

Apache Flink

Optimizer + SQL support
	•	Flink Table API “Concepts & Common API”: the optimizer is documented as
“Converts NOT IN and NOT EXISTS into left anti-join. Optional join reordering.”  ￼
This is explicit proof that NOT IN / NOT EXISTS are supported and get compiled to left anti-join operators in Flink’s planner.

Runtime operator
	•	StreamingSemiAntiJoinOperator Javadoc: describes the streaming runtime operator that implements semi/anti joins and how it emits insert/delete records depending on matches on the “other side” of the join.  ￼
That’s the actual code-level implementation of streaming anti-joins.

Usage in practice
	•	German Flink article (“Anwendungen von Apache Flink und Ausblick in die Zukunft”) notes that the SQL query optimizer was enhanced with additional runtime operators, explicitly including semi- and anti-join operators.  ￼
	•	A Chinese Flink SQL Q&A from Alibaba Cloud shows practical advice to switch from LEFT JOIN to LEFT ANTI JOIN in a production Flink SQL job when the right side only exists for some keys.  ￼

These together show: (1) NOT EXISTS/NOT IN → anti-join is an official feature, (2) there is a dedicated streaming operator, and (3) people are using left anti joins in real Flink jobs.

⸻

Kafka Streams

Tombstones & KTable semantics
	•	KTable Javadoc (Confluent and Apache):
“records with null values (so-called tombstone records) have delete semantics. … for each record that gets dropped … a tombstone record is forwarded.”  ￼
This is the core mechanism by which “key disappeared” events are propagated and then affect joins.

Joins and tombstones
	•	Kafka Streams DSL docs describe KTable–KTable equi-joins and explicitly say that tombstones participate in updating join results (though they “do not trigger the join” in some cases).  ￼
	•	Confluent blog “Crossing the Streams – Joins in Apache Kafka” analyzes KTable–KTable joins and notes that the join wrote tombstone records to the result KTable, which were later compacted away.  ￼

These show that anti-like behavior (“remove this output row when the right side disappears”) is implemented via tombstones and used in real join examples.

⸻

Apache Spark / Structured Streaming

Left anti join as an official join type
	•	PySpark DataFrame.join docs list "left_anti" as a join type and show an example:
df.join(df2, "name", "left_anti").show() returning rows in the left with no match in the right.  ￼

This is the canonical Spark anti-join.

Limitations in stream–stream joins
	•	Databricks “Work with joins” / stream-stream join docs list only inner, left/right/full outer, and left semi joins as supported for stream–stream joins; left anti is not in that list.  ￼
	•	A StackOverflow answer about updating a static DataFrame with streaming data notes that people have tried except() and 'left_anti' in Structured Streaming, but they hit limitations because the static side is just used as a lookup and not updated.  ￼

So Spark very clearly has left-anti joins in the core API, but for stream–stream use you’re restricted; stream-static anti-joins are used but have caveats.

⸻

Materialize

Set difference (EXCEPT) and incremental maintenance
	•	SELECT documentation lists EXCEPT as part of Materialize SQL, explicitly defining it as “Records present in select_stmt but not in another_select_stmt.”  ￼
	•	The same SELECT page emphasizes that a SELECT on an indexed source, view or materialized view returns “maintained results from memory,” i.e., results are incrementally updated.  ￼
	•	CREATE MATERIALIZED VIEW docs:
“…the SELECT statement whose results you want to maintain incrementally updated.”  ￼

That’s direct evidence that set-difference style queries (EXCEPT) are supported and maintained incrementally.

Subquery / negation internals
	•	Blog post “How Materialize and other databases optimize SQL subqueries (decorrelation)” shows query plans where relational ops like LEFT JOIN are reduced to combinations of smaller differential dataflow operators, including negate (the primitive underlying set difference / NOT EXISTS behavior).  ￼
	•	A report on bridging IVM and stream processing (He, “Bridging the gap between Incremental View Maintenance and stream processing”) discusses left/right anti-joins and describes how to maintain them efficiently with hash maps, explicitly citing Materialize as a representative system.  ￼
	•	A recent IVM survey (“Ease Across the Latency Spectrum with Delayed View Maintenance”) describes Materialize as a torchbearer of IVM-based stream processing and explicitly mentions that this family of systems supports the full relational algebra, including anti-join derivatives.  ￼

Together: Materialize exposes EXCEPT in SQL, materializes those queries incrementally, and its own and external papers discuss anti-join/negation as a first-class part of the execution model.

⸻

Differential Dataflow / DBSP

Library API
	•	A GitHub issue on differential-dataflow explains that antijoin() is implemented in terms of semijoin(), and discusses its argument types and arrangement sharing.  ￼

That’s a direct confirmation that there is an antijoin operator in the public API.

Papers & systems built on it
	•	The DBSP paper (“DBSP: Automatic Incremental View Maintenance for Rich Query Languages”) explicitly mentions transforming an anti-join into a join followed by a set difference as part of its semantics and optimization rules.  ￼
	•	A VLDB-accepted paper on FlowLog / incremental Datalog (“FlowLog: Efficient and Extensible Datalog via Incrementality”) describes the semantics of antijoin over differential dataflow, including an example where antijoin yields a particular output with differential updates.  ￼
	•	Other academic work on incremental modeling with differential dataflow (e.g., Zhang’s “Towards a Semantic Backplane for Incremental Modeling”) list antijoin alongside map/filter/join as one of the base operators implemented over differential dataflow.  ￼

So: anti-join is part of the formal algebra of differential dataflow, with explicit mention in APIs and several research systems built on it.

⸻

RisingWave

Native semi/anti joins
	•	RisingWave’s blog post “Understanding Streaming Joins in RisingWave” explicitly states:
“RisingWave join implementation also supports semi-joins and anti-joins, but they cannot be directly expressed in join syntax and need to be written as correlated subqueries.”  ￼
It also explains that RisingWave rewrites correlated subqueries into APPLY operators and then into joins following the classic “Unnesting Arbitrary Queries” paper.

Set operations (EXCEPT)
	•	RisingWave SQL docs on Set operations list UNION, INTERSECT, and EXCEPT and explain how EXCEPT works, with a CORRESPONDING extension.  ￼
	•	A RisingWave 2.0 feature blog highlights support for EXCEPT with CORRESPONDING, again confirming that set-difference is part of the production SQL dialect.  ￼

This is pretty strong: the vendor itself says “we support semi- and anti-joins” (internally via correlation/unnesting), and they expose EXCEPT in the SQL surface.

⸻

Pathway

Here the interesting fact is absence of full anti-join support:
	•	Pathway’s SQL docs list supported operations for pw.sql. They support WHERE, joins, UNION, INTERSECT, etc., but explicitly say:
“For now, only single row result subqueries are supported. Correlated subqueries and the associated operations ANY, NONE, and EVERY (or ALL) are currently not supported.”  ￼
	•	It also warns that GROUP BY and JOIN should not be used in a single SELECT and that NATURAL/FULL JOIN aren’t yet supported.  ￼

Given anti-join in SQL is typically expressed as WHERE NOT EXISTS (correlated subquery) or LEFT JOIN … WHERE right IS NULL, this doc is evidence that Pathway currently doesn’t expose full anti-join/NOT EXISTS machinery over streaming tables, beyond what you can manually emulate with the limited subset.

⸻

Spark & anti-join in streaming pipelines (usage evidence)

Besides the core API docs, there are practitioner writeups showing these features used in real jobs:
	•	A short article “Left Anti Join in dataset spark java” explains left anti join semantics (“rows from the first dataset which do not have a match in the second dataset”) and gives code examples.  ￼
	•	A more recent Spark article building a real-time analytics pipeline with Kafka + Spark Structured Streaming shows joined_anti = stream_df.join(dim_df, "key", "left_anti") as part of the job.  ￼

This is not official doc, but it’s concrete evidence that people use left-anti joins in Spark for production pipelines.

⸻

Kafka Streams & tombstone use (usage evidence)

Beyond pure API docs:
	•	The Confluent blog “Crossing the Streams – Joins in Apache Kafka” walks through an example where a KTable–KTable join produces tombstone records in the result KTable and explains how they are compacted away.  ￼
	•	A Kafka Streams Q&A specifically about “KTable KTable join tombstone” discusses how tombstones from a join are distinguished from explicit tombstones, indicating teams rely on KTable join/tombstone semantics in real apps.  ￼

These show that delete/tombstone semantics, which you’d use for anti-join-style “unmatched” tracking, are very much in live use.

⸻

Ecosystem / survey-level evidence

If you want higher-level confirmation that anti-joins and relatives are part of the core feature set of modern IVM/streaming DBs:
	•	The delayed view-maintenance survey (“Ease Across the Latency Spectrum with Delayed View Maintenance”, 2025) notes that the last half-decade has produced a “cornucopia of IVM-based stream processing systems,” led by Materialize and including RisingWave and Feldera (DBSP), and explicitly mentions that they implement anti-join derivatives as part of full relational algebra on streams.  ￼

That’s essentially the meta-claim: in this ecosystem, anti-join/NOT-EXISTS/EXCEPT aren’t exotic; they’re standard algebraic operators that the engines and query planners understand and optimize.

⸻

Future work

Possible next steps include extracting a small number of concrete code snippets for selected systems (e.g., Flink, Kafka Streams, DBSP/Feldera) and mapping them directly to the (a)/(b)/(c) incremental-maintenance cases in the original research prompt.
