# 「代数的数を作る 多項式の根と因数分解のアルゴリズム」

このリポジトリーは、[「代数的数を作る 多項式の根と因数分解のアルゴリズム」](https://lab.miz-ar.info/algebraic-num/)のサンプルコードを納めたものです。

サンプルコードの実行には[Haskell Stack](https://docs.haskellstack.org/en/stable/README/)が必要です。あらかじめインストールしておいてください。

次のコマンド

```sh
$ git clone https://github.com/minoki/algebraic-num-example.git
$ cd algebraic-num-example
```

によってリポジトリーをチェックアウトした後、以下のように各チャプターに対応するブランチに切り替えることができます：

* \#1 一変数多項式環
    * `$ git checkout chap01`
* \#2 実根の数え上げ
    * `$ git checkout chap02`
* \#3 代数的数の演算と終結式
    * `$ git checkout chap03`
* \#4 擬除算と多項式剰余列
    * `$ git checkout chap04`
* \#5 区間演算と計算可能実数
    * `$ git checkout chap05`
* \#6 代数的数の演算まとめ
    * `$ git checkout chap06`
* \#7 整域と整数係数多項式
    * `$ git checkout chap07`
* \#8 多項式の因数分解 その1 Kroneckerの方法と無平方分解
    * `$ git checkout chap08`
* \#9 有限体
    * `$ git checkout chap09`
* \#10 多項式の因数分解 その2 Cantor-Zassenhausの方法
    * `$ git checkout chap10`
* \#11 多項式の因数分解 その3 Berlekampの方法
    * `$ git checkout chap11`
* \#12 多項式の因数分解 その4 整数係数の因数分解と代数的数の最小多項式
    * `$ git checkout chap12`
* \#13 多項式の因数分解 その5 Henselの補題
    * `$ git checkout chap13`
* \#14 代数的実数を係数とする代数方程式
    1. 初期バージョン（素朴なゼロ判定）: `$ git checkout chap14-1`
    2. 区間演算によるゼロ判定: `$ git checkout chap14-2`
    3. スツルムの定理によるゼロ判定: `$ git checkout chap14-3`
    4. 区間の端点での符号によるゼロ判定: `$ git checkout chap14-4`
* \#15 虚根の数え上げ、そして代数閉体へ（前編）: コード例なし
* \#16 虚根の数え上げ、そして代数閉体へ（後編）
    * `$ git checkout chap16`
* 付録B 部分分数分解
    * `$ git checkout app02`

サンプルコードをREPLで試す場合は、各ブランチに切り替えた状態で

```sh
$ stack repl
```

を実行します。`stack`を初めて実行する場合は諸々のインストールが行われるので時間がかかりますが、2回目以降はそれほど時間はかからないはずです。
