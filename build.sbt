scalaVersion in ThisBuild := sys.env.getOrElse("DOTTY_VERSION", dottyLatestNightlyBuild.get)
scalacOptions in ThisBuild := Seq("-language:Scala2")
