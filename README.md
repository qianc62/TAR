The main class for testing is com.iise.shudi.exroru.evaluation.SingleTimeAnalysis. You can modify the constant "ROOT_FOLDER" to change the folder containing the models to run the program and see the testing results for GENERAL algorithm, IMPROVED and RG based algorithm.

(For the algorithms from the related work (i.e. JIN and ZHA), they were implemented as part of the previous BEEHIVEZ tool, which makes it hard to isolate them from the original project they depend on. Therefore they are not included in this package. In case you want to acquire their implementations, please contact Jisheng Pei by 12283776@qq.com )

This project can be imported to Eclipse or IntelliJ IDEA. Please do not forget to import the jar files in lib.

Be sure to compile all the source code using JDK 1.8 or above!

Under the "models/bounded-models" archive you may find 5 process model repositories for effectiveness evaluation. For their detailed descriptions, please refer to the experiment section of our paper, and also the article [12] in reference.

Under the "models/1-safe-models" archive you may find, again, 5 process model repositories for effectiveness evaluation. They are 1-safe nets extracted from the above bounded-models archive. For their detailed descriptions, please refer to the experiment section of our paper, and also the article [12] in reference.

There are two process model repositories in models/scalability for scalability testing purpose. breadth folder contains sound free-choice WF-nets with different numbers of concurrent branches. depth folder contains sound free-choice WF-nets with different numbers of sequential transitions on each branches.

If you have any question about this project, please send email to Jisheng Pei (12283776@qq.com) or Lijie Wen (6939192@qq.com).