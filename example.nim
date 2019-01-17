import interfaced

createInterface(Runnable):
   proc run()

createInterface(Worker, Runnable):
   proc work()

createInterface(Animal, Worker):
   proc makeNoise(): string
   proc legs(x: Animal): int
   proc legs(x: Animal): int
   proc legs(x: Animal, m: int): int
   proc greet(other: string): string

createInterface(BigAnimal, Animal):
   proc say()

type
   Dog* = ref object
      name: string
      age: int

   Cat = ref object
      name: string

proc makeNoise(d: Dog): string = d.name & " is barking"
proc legs(d: Dog): int = 4
proc legs(d: Dog, m: int): int = 4 + m
proc greet(d: Dog, other: string): string = "Welcome " & other & " from dog " & d.name
proc `$`(d: Dog): string = "Dog " & d.name
proc run(d: Dog) = echo $d, " will run"
proc work(d: Dog) = echo $d, " can work"
proc say(d: Dog) = echo $d, " is so big"

proc makeNoise(d: Cat): string = d.name & " is meoming"
proc legs(d: Cat): int = 8
proc legs(d: Cat, m: int): int = 8 + m
proc greet(d: Cat, other: string): string = "Welcome " & other & " from cat " & d.name
proc `$`(d: Cat): string = "Cat " & d.name
proc run(d: Cat) = echo $d, " is running"
proc work(d: Cat) = echo $d, " cannot work"

Dog.impl(Worker, BigAnimal)
Cat.impl(Animal)

proc takeRun(x: Runnable) =
   x.run()

proc takeWork(x: Worker) =
   x.work()

proc action(x: Animal) =
   echo "I am ", x
   echo x.makeNoise
   echo "I have ", x.legs, " legs"
   echo "I have ", x.legs(3), " more legs"
   x.takeRun
   x.takeWork

proc action(xs: seq[Animal]) =
   for x in xs:
      action(x)
      echo ""

when isMainModule:
   var xs = new_seq[Animal]()

   let
      d = Dog(name: "Bob").toBigAnimal
      c = Cat(name: "Mimi")

   xs.add d
   xs.add c
   action(xs)
