# Arduino Programming Examples
All of these examples assume a button (pulled-down) on pin 2 and an LED on pin 8.

## Toggle on Click (polling)
```C
const int BUTTON = 2;
const in LED = 8;

int buttonState;
int ledState;

void setup() {
    pinMode(LED, OUTPUT);
    pinMode(BUTTON, INPUT);

    ledState = LOW;
    digitalWrite(LED, ledState);

    buttonState = digitalRead(BUTTON);
}

void loop() {
    int oldState = buttonState;
    buttonState = digitalRead(BUTTON);

    if (oldState == LOW && buttonState == HIGH) {
        ledState = !ledState;
        digitalWrite(LED, ledState);
    }
}
```

## Toggle on Click (interrupt)
```C
const int BUTTON = 2;
const int LED = 8;

int buttonState;

void toggle() {
    ledState = !ledState;
    digitalWrite(LED, ledState);
}

void setup() {
    pinMode(LED, OUTPUT);
    pinMode(BUTTON, INPUT);

    ledState = LOW;
    digitalWrite(LED, ledState);

    attachInterrupt(digitalPinToInterrupt(BUTTON), toggle, RISING);
}

void loop() { }
```

## Light while Pressed
```C
void setup() {
    pinMode(LED, OUTPUT);
    pinMode(BUTTON, INPUT);
}

void loop() {
    digitalWrite(LED, digitalRead(BUTTON));
}
```

## Turn on once pressed
```C
void setup() {
    pinMode(LED, OUTPUT);
    pinMode(BUTTON, INPUT);

    digitalWrite(LED, LOW);
}

void loop() {
    if (digitalRead(BUTTON) == HIGH) {
        digitalWrite(LED, HIGH);
    }
}
```
