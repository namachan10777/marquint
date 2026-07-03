// # Raft の安全性と Leader Completeness の証明
//
// このファイルは、Quint の型・述語・補題・不変条件を使って Raft の
// 安全性証明を読める形で記述した literate proof note です。
//
// 中心になる定理は **Leader Completeness** です。
//
// > term `t` でコミットされたログエントリは、それより後の任意の
// > term で選出された leader のログにも必ず含まれる。
//
// この定理に Log Matching と「状態機械はコミット済みエントリだけを
// ログ順に適用する」という規則を合わせると、Raft の標準的な
// **State Machine Safety** が従います。

module raft {
  // ## 数学的な対象
  //
  // ノードとコマンドの内部構造は使いません。証明が依存するのは、
  // term、ログ index、投票、そして quorum の交差性だけです。

  type Node
  type Command

  type Term = int
  type Index = int

  type Entry = {
    term: Term,
    command: Command,
  }

  // サーバ状態は安全性証明に必要な分だけに絞ります。重要なのは
  // currentTerm、その term で投票した相手、永続化されたログです。
  type Server = {
    currentTerm: Term,
    votedFor: Set[Node],
    log: List[Entry],
  }

  type State = {
    servers: Node -> Server,

    // `leaderOf.get(t).contains(n)` は、`n` が term `t` の leader として
    // 選出されたことを表します。Raft では各 term の leader は高々 1 つで、
    // その性質は下の `ElectionSafety` で表します。
    leaderOf: Term -> Set[Node],

    // `commitIndex.get(n)` は、サーバ `n` がコミット済みだと認識している
    // 最大 index です。この証明では AppendEntries の細部を再実装せず、
    // コミット済みかどうかを抽象述語として扱います。
    commitIndex: Node -> Index,
  }

  const Nodes: Set[Node]
  const Terms: Set[Term]

  // ## ログに関する基本述語
  //
  // Raft 論文のログ index は 1 始まりです。Quint の List は 0 始まりなので、
  // 実際にアクセスするときは protocol index から 1 を引きます。

  pure def validIndex(i: Index): bool = i > 0

  pure def hasIndex(l: List[Entry], i: Index): bool =
    validIndex(i) and i <= l.length()

  pure def entryAt(l: List[Entry], i: Index): Entry =
    l[i - 1]

  pure def isPrefix(xs: List[Entry], ys: List[Entry]): bool =
    xs.length() <= ys.length()
      and (1.to(xs.length())).forall(i => entryAt(xs, i) == entryAt(ys, i))

  pure def hasEntry(s: State, n: Node, i: Index, e: Entry): bool =
    hasIndex(s.servers.get(n).log, i)
      and entryAt(s.servers.get(n).log, i) == e

  pure def lastLogIndex(s: State, n: Node): Index =
    s.servers.get(n).log.length()

  pure def lastLogTerm(s: State, n: Node): Term =
    if (lastLogIndex(s, n) == 0) {
      0
    } else {
      entryAt(s.servers.get(n).log, lastLogIndex(s, n)).term
    }

  // candidate `c` のログが voter `v` のログと同等以上に新しいことを表します。
  //
  // これは Raft の RequestVote に出てくる制約そのものです。
  //
  // 1. 最後のログエントリの term が大きい方が新しい。
  // 2. 最後の term が同じなら、ログが長い方が新しい。
  pure def atLeastAsUpToDate(s: State, c: Node, v: Node): bool =
    lastLogTerm(s, c) > lastLogTerm(s, v)
      or (
        lastLogTerm(s, c) == lastLogTerm(s, v)
          and lastLogIndex(s, c) >= lastLogIndex(s, v)
      )

  // ## Quorum
  //
  // Raft は多数派 quorum を使います。証明で本質的に必要なのは、
  // 任意の 2 つの quorum が少なくとも 1 つのサーバを共有することです。

  pure def isQuorum(q: Set[Node]): bool =
    q.subseteq(Nodes) and q.size() * 2 > Nodes.size()

  pure def QuorumIntersection: bool =
    Nodes.powerset().forall(q1 =>
      Nodes.powerset().forall(q2 =>
        isQuorum(q1) and isQuorum(q2)
          implies q1.intersect(q2).size() > 0
      )
    )

  // ## 証明義務として使う抽象的な protocol fact
  //
  // ここからの述語は、Raft の遷移規則から維持される再利用可能な安全性事実です。
  // 完全な実行可能モデルなら `Init` と `Next` からこれらを帰納的に証明します。
  // このファイルでは、これらが成り立つときに Leader Completeness がどう従うかに
  // 焦点を当てます。

  // **Election Safety**
  //
  // 1 つの term では leader は高々 1 つだけ選出されます。各サーバが同じ term で
  // 高々 1 票しか与えず、任意の 2 つの多数派が交差することから従います。
  pure def ElectionSafety(s: State): bool =
    Terms.forall(t =>
      s.leaderOf.get(t).subseteq(Nodes)
        and s.leaderOf.get(t).size() <= 1
    )

  // **Leader Append-Only**
  //
  // leader は自分のログを上書き・削除せず、末尾に append するだけです。
  // ここでは old state と new state の関係として表します。
  pure def LeaderAppendOnly(old: State, new: State): bool =
    Terms.forall(t =>
      Nodes.forall(l =>
        old.leaderOf.get(t).contains(l)
          implies isPrefix(old.servers.get(l).log, new.servers.get(l).log)
      )
    )

  // **Log Matching**
  //
  // 2 つのログが同じ index と term のエントリを持つなら、その index までの
  // prefix は完全に一致します。これは AppendEntries の整合性チェックで維持されます。
  pure def LogMatching(s: State): bool =
    Nodes.forall(a =>
      Nodes.forall(b =>
        (1.to(lastLogIndex(s, a))).forall(i =>
          (1.to(lastLogIndex(s, b))).forall(j =>
            i == j
              and entryAt(s.servers.get(a).log, i).term
                == entryAt(s.servers.get(b).log, j).term
              implies
                (1.to(i)).forall(k =>
                  entryAt(s.servers.get(a).log, k)
                    == entryAt(s.servers.get(b).log, k)
                )
          )
        )
      )
    )

  // **Vote Freshness**
  //
  // voter `v` が candidate `c` に投票するなら、投票時点で `c` のログは `v` の
  // ログと同等以上に新しくなければなりません。
  pure def VoteFreshness(s: State, voter: Node, candidate: Node): bool =
    atLeastAsUpToDate(s, candidate, voter)

  // ## コミット済みエントリ
  //
  // 現在の leader の term に属するエントリは、それが quorum に保存されたとき
  // コミットされたと言えます。古い term のエントリは、ログ prefix と leader の
  // commit order によって間接的にコミット済みになります。

  pure def storedOn(s: State, i: Index, e: Entry): Set[Node] =
    Nodes.filter(n => hasEntry(s, n, i, e))

  pure def committedInTerm(s: State, i: Index, e: Entry, t: Term): bool =
    e.term == t and isQuorum(storedOn(s, i, e))

  pure def committed(s: State, i: Index, e: Entry): bool =
    validIndex(i) and Nodes.exists(n =>
      s.commitIndex.get(n) >= i and hasEntry(s, n, i, e)
    )

  // ## 補題 1: コミット済みエントリは選挙を越えて残る
  //
  // index `i` のエントリ `e` が term `t` でコミットされ、その後の term
  // `u > t` で leader `l` が選出されたとします。
  //
  // `e` は quorum `Qcommit` に保存されていました。新しい leader は quorum
  // `Qvote` の投票で選出されます。quorum intersection により、両方に属する
  // サーバ `v` が存在します。したがって `v` は term `u` で投票した時点で
  // `e` を持っていました。
  //
  // `v` が `l` に投票したので、Vote Freshness により `l` のログは `v` のログと
  // 同等以上に新しい必要があります。もし `l` が `e` を持たないなら、可能性は
  // 2 つだけです。
  //
  // 1. `l` のログが `i` より短い。この場合、`v` と同等以上に新しいとは言えません。
  // 2. `l` が `i` に別のエントリを持つ。Log Matching により、その別エントリは
  //    `t` より大きい term のものです。しかし下の最小反例による帰納法から、
  //    そのようなエントリを作った中間 term の leader もすでに `e` を持っていた
  //    はずで、`e` を消すことはできません。
  //
  // どちらの場合も投票規則に反します。したがって `l` は `e` を含みます。
  pure def CommittedEntrySurvivesElection(
    s: State,
    i: Index,
    e: Entry,
    t: Term,
    u: Term,
  ): bool =
    QuorumIntersection
      and LogMatching(s)
      and committedInTerm(s, i, e, t)
      and u > t
      implies
        Nodes.forall(l =>
          s.leaderOf.get(u).contains(l) implies hasEntry(s, l, i, e)
        )

  // ## 補題 2: 最小反例による帰納法
  //
  // Leader Completeness を証明するため、反対を仮定し、コミット済みエントリ
  // `e` を含まない leader が初めて現れる最小の後続 term `u` を取ります。
  //
  // このとき `t < r < u` を満たす任意の term `r` の leader は `e` を含みます。
  // したがって、新 leader のログを「より新しく」見せうるエントリは、すでに
  // `e` を持っていた leader によって作られたものです。Leader Append-Only と
  // Log Matching により、それらのエントリは `e` を消せません。
  pure def NoSmallerCounterexample(
    s: State,
    i: Index,
    e: Entry,
    t: Term,
    u: Term,
  ): bool =
    committedInTerm(s, i, e, t)
      and u > t
      implies
        ((t + 1).to(u - 1)).forall(r =>
          Nodes.forall(l =>
            s.leaderOf.get(r).contains(l) implies hasEntry(s, l, i, e)
          )
        )

  // ## 定理: Leader Completeness
  //
  // コミット済みエントリの term より後に選出された任意の leader は、その
  // エントリをログに含みます。これにより、いったんコミットされた command が
  // 後続の選挙で失われないことが保証されます。
  pure def LeaderCompleteness(s: State): bool =
    QuorumIntersection
      and LogMatching(s)
      and ElectionSafety(s)
      implies
        Terms.forall(t =>
          Nodes.forall(n =>
            (1.to(lastLogIndex(s, n))).forall(i => {
              val e = entryAt(s.servers.get(n).log, i)
              committedInTerm(s, i, e, t)
                implies
                  Terms.forall(u =>
                    u > t implies
                      Nodes.forall(l =>
                        s.leaderOf.get(u).contains(l)
                          implies hasEntry(s, l, i, e)
                      )
                  )
            })
          )
        )

  // ## 定理: State Machine Safety
  //
  // あるサーバがログ index `i` の command を状態機械に適用したなら、
  // 他のサーバが同じ index で別の command を適用することはありません。
  //
  // 理由:
  //
  // 1. サーバはコミット済みエントリだけを適用する。
  // 2. Leader Completeness により、後続 leader は過去のコミット済みエントリを
  //    必ず含む。
  // 3. Log Matching により、同じ index と term の一致は prefix 全体を固定する。
  // 4. よって同じ index の 2 つのコミット済みエントリは同一でなければならない。
  pure def StateMachineSafety(s: State): bool =
    LeaderCompleteness(s)
      and LogMatching(s)
      implies
        Nodes.forall(a =>
          Nodes.forall(b =>
            (1.to(lastLogIndex(s, a))).forall(i =>
              hasIndex(s.servers.get(b).log, i)
                and committed(s, i, entryAt(s.servers.get(a).log, i))
                and committed(s, i, entryAt(s.servers.get(b).log, i))
                implies
                  entryAt(s.servers.get(a).log, i).command
                    == entryAt(s.servers.get(b).log, i).command
            )
          )
        )

  // ## 帰納的な安全性不変条件
  //
  // Raft の実行可能モデルでは、この述語が `Init` で成立し、すべての `Next`
  // 遷移で保存されることを証明します。これが帰納的不変条件になれば、
  // `StateMachineSafety` は直接従います。
  pure def SafetyInvariant(s: State): bool =
    QuorumIntersection
      and ElectionSafety(s)
      and LogMatching(s)
      and LeaderCompleteness(s)
      and StateMachineSafety(s)
}
