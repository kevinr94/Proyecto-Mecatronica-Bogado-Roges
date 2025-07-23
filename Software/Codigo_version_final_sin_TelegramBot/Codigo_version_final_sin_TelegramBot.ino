#include "DHTesp.h"
#include <Wire.h>			
#include <Adafruit_GFX.h>		
#include <Adafruit_SSD1306.h>
#include <OneWire.h> 
#include <DallasTemperature.h>
#include <ESP32Servo.h>
#include "esp_task_wdt.h"
//Pulsadores del panel
#define menu_ok  12 //Botón para entrar a menu o volver
#define menu_up  14 // Botón para aumentar valores
#define menu_down  27 //Botón para decrecer valores
#define menu_config  26 //Botón confirmación
#define VENTILACION 2
#define ILUMINACION 0
#define BOMBA 4
#define EV1 16
#define EV2 17
#define EV3 5
#define NIVEL 19 // Sensor de nivel
#define activar_sensores 13
bool sensor_ph=false; //en false activa pH. En true activa TDS
//tds
#define TdsSensorPin 34
#define VREF 3.3              // analog reference voltage(Volt) of the ADC
#define SCOUNT  30            // sum of sample point
int analogBuffer[SCOUNT];     // store the analog value in the array, read from ADC
int analogBufferTemp[SCOUNT];
int analogBufferIndex = 0;
int copyIndex = 0;
float averageVoltage = 0;
float tdsValue = 0;
float temperature = 25;       // current temperature for compensation
// median filtering algorithm
int getMedianNum(int bArray[], int iFilterLen){
  int bTab[iFilterLen];
  for (byte i = 0; i<iFilterLen; i++)
  bTab[i] = bArray[i];
  int i, j, bTemp;
  for (j = 0; j < iFilterLen - 1; j++) {
    for (i = 0; i < iFilterLen - j - 1; i++) {
      if (bTab[i] > bTab[i + 1]) {
        bTemp = bTab[i];
        bTab[i] = bTab[i + 1];
        bTab[i + 1] = bTemp;
      }
    }
  }
  if ((iFilterLen & 1) > 0){
    bTemp = bTab[(iFilterLen - 1) / 2];
  }
  else {
    bTemp = (bTab[iFilterLen / 2] + bTab[iFilterLen / 2 - 1]) / 2;
  }
  return bTemp;
}
//tds
//ph
#define pHpin  35
#define VREF 3.3               // voltaje de referencia ADC ESP32
#define pH_SAMPLES 30          // cantidad de muestras a promediar
int pHBuffer[pH_SAMPLES];      // buffer circular
int pHBufferTemp[pH_SAMPLES];  // copia para filtrar
int pHIndex = 0;               // índice de inserción
float pH = 7.0;                // valor final de pH
float slope = -5.315;           // calibración (ajustar según tu sensor)
float offset = 21.87;          // calibración (ajustar según tu sensor)
int calcularMediana(int datos[], int cantidad) {
  int copiaDatos[cantidad];
  for (int i = 0; i < cantidad; i++) {
    copiaDatos[i] = datos[i];
  }

  for (int j = 0; j < cantidad - 1; j++) {
    for (int i = 0; i < cantidad - j - 1; i++) {
      if (copiaDatos[i] > copiaDatos[i + 1]) {
        int temp = copiaDatos[i];
        copiaDatos[i] = copiaDatos[i + 1];
        copiaDatos[i + 1] = temp;
      }
    }
  }

  if (cantidad % 2 == 1) {
    return copiaDatos[cantidad / 2];
  } else {
    return (copiaDatos[cantidad / 2] + copiaDatos[(cantidad / 2) - 1]) / 2;
  }
}
//ph
#define ANCHO 128  //Parametro de pantalla Oled	
#define ALTO 64	
#define OLED_RESET 4			
int menu = 0;
int menu2 = 0;
int menu3 = 0;
int etapa = 1; //identifi a numero de etapa
int dia_obj = 1; //cantidad de dias de etapa
float ph_min = 4.0;//pH minimo
float ph_max = 7.0; //pH maximo
int ec_min = 500; //ec min
int ec_max = 1500; //ec max
bool estadoVent = false;
bool estadoVentAnterior = false;
bool estadoIlum = false;
bool estadoIlumAnterior = false;
bool estadoBomba = false;
bool estadoEv1 = false;
bool estadoEv2 = false;
bool estadoEv3 = false;
bool estadoServo = false;
#define oneWireBus  23 //Sensor temperatura liquido
float temperatureC;
OneWire oneWire(oneWireBus);
DallasTemperature sensors(&oneWire);
Adafruit_SSD1306 display(ANCHO, ALTO);	
int pinDHT = 15; //Iniciamos sensor DHT22
DHTesp dht;
// Electroconductividad (EC) [milisiemens por centímetro (mS/cm)] y Sólidos Disueltos Totales (TDS) [ppm]
float ecPromedio = 0.0;
float tds = 0.0;
Servo miServo;  // crea el objeto servo
const int pinServo = 25; // Pin GPIO al que está conectado el servo
static unsigned long lastDebounceTime = 0;
unsigned long tiempoDebounce = 300; //tiempo debounce botones

//Parametros del programa
bool inicio_programa = false;
int dias_transcurridos = 0;
unsigned long inicioCicloMillis = 0;
unsigned long duracionBomba = 2UL * 60UL * 60UL * 1000UL; // 2 horas en milisegundos
unsigned long intervalo12h = 12UL * 60UL * 60UL * 1000UL; // 12 horas en milisegundos
unsigned long ultimoCicloMillis = 0;
bool cicloActivo = false;
bool ecListo = false;
bool phListo = false;
unsigned long tiempoInicioPrograma = 0;
bool primerInicio = true;
unsigned long tiempo_dia_anterior = 0;
const unsigned long INTERVALO_DIA = 24UL * 60UL * 60UL * 1000UL; // 24 hs en ms
//unsigned long duracionBomba = 10UL * 60UL * 1000UL; // 5 minutos VARIABLES DE PRUEBA
//unsigned long intervalo12h = 15UL * 60UL * 1000UL; // 15 minutos VARIABLES DE PRUEBA
//const unsigned long INTERVALO_DIA = 30UL * 60UL * 1000UL; // 30 minutos VARIABLES DE PRUEBA
static unsigned long tiempoInicioLuz = 0;  // <-- NUEVO
const unsigned long INTERVALO_LUZ_ENCENDIDA = 16UL * 60UL * 60UL * 1000UL; // 16 horas
unsigned long tiempoEsperaPH = 0;
unsigned long tiempoEsperaSegundaMedicion = 0;
bool esperaPHIniciada = false;
bool segundaMedicionHecha = false;
bool enEsperaSegundaMedicion = false;
bool segundaECListo = false;
bool segundaPHListo = false;
unsigned long tiempoEsperaPH_2 = 0;
bool aviso_medicion_ph;
bool aviso_ph_fin;
bool segundaMedicionECHecha = false;
bool segundaMedicionPHHecha = false;
//Variables de sensores pH y EC. Necesarias aca, para luego poder reinciiar
static unsigned long ultimaEjecucion1 = 0;
static unsigned long inicioInyeccion1 = 0;
static bool inyectando1 = false;
static bool esperando1 = false;
static int lecturasCorrectas1 = 0;
static unsigned long ultimaEjecucion = 0;
static unsigned long inicioInyeccion = 0;
static bool inyectando = false;
static bool esperando = false;
static int lecturasCorrectas = 0;
//
unsigned long ultimaLecturaTemp = 0;
bool esperandoTemperatura = false;


void setup() {
  pinMode(menu_ok, INPUT_PULLDOWN);
  pinMode(menu_up, INPUT_PULLDOWN);
  pinMode(menu_down, INPUT_PULLDOWN);
  pinMode(menu_config, INPUT_PULLDOWN);
  pinMode(NIVEL, INPUT_PULLUP);
  pinMode(VENTILACION, OUTPUT);
  pinMode(ILUMINACION, OUTPUT);
  pinMode(BOMBA, OUTPUT);
  pinMode(EV1, OUTPUT);
  pinMode(EV2, OUTPUT);
  pinMode(EV3, OUTPUT);
  digitalWrite(VENTILACION, HIGH);
  digitalWrite(ILUMINACION, HIGH);
  digitalWrite(BOMBA, HIGH);
  digitalWrite(EV1, HIGH);
  digitalWrite(EV2, HIGH);
  digitalWrite(EV3, HIGH);
  pinMode(TdsSensorPin,INPUT);
  miServo.attach(pinServo);
  pinMode(activar_sensores, OUTPUT);
  analogReadResolution(12);                // 12 bits → 0–4095
  analogSetPinAttenuation(pHpin, ADC_11db);      // rango 0–3.3 V
  analogSetPinAttenuation(TdsSensorPin, ADC_11db);
  sensors.begin();  // Iniciar sensor
  Wire.begin();
  Wire.setClock(100000);
  Serial.begin(115200);	
  display.begin(SSD1306_SWITCHCAPVCC, 0x3C);
  display.setTextSize(1);           
  display.setTextColor(SSD1306_WHITE);
  display.setCursor(10,40);
  display.display();
  //Inicializamos el dht
  dht.setup(pinDHT, DHTesp::DHT22);
  // Inicializa el watchdog para el task actual (loop)
  esp_task_wdt_config_t wdt_config = {
    .timeout_ms = 8000,     // 8 segundos
    .idle_core_mask = 1,    // núcleo 0
    .trigger_panic = true   // reinicia si no se alimenta
  };
  esp_reset_reason_t reason = esp_reset_reason();
  Serial.print("Motivo del último reset: ");
  Serial.println(reason);
  esp_task_wdt_init(&wdt_config);
  esp_task_wdt_add(NULL);  // Añade la tarea actual (loop)
}

void loop(){
  lecturaTemperatura(); 
  TempAndHumidity data = dht.getTempAndHumidity(); //Obtención de temperatura y humedad de DHT22
  relay_bomba();
  relay_ilum();
  relay_vent();
  relay_ev1();
  relay_ev2();
  relay_ev3();
  servo_sensor();
  lecturaTDS();
  lecturapH();
  lectura_sensores();
  display.clearDisplay();
  // Inicio del programa
if (inicio_programa == true) {
    if (dias_transcurridos <= dia_obj) {
      unsigned long tiempoActual = millis();
      if (primerInicio || (tiempoActual - ultimoCicloMillis >= intervalo12h)) {// Iniciar un nuevo ciclo de 2 horas
        inicioCicloMillis = tiempoActual;
        ultimoCicloMillis = tiempoActual;
        cicloActivo = true;
        estadoBomba = true;
        ecListo = false;
        phListo = false;
        primerInicio = false;
        tiempoInicioLuz = millis(); // para control de luz (pero no prenderá inmediatamente)
        esperaPHIniciada = false;
        segundaMedicionHecha = false;
        enEsperaSegundaMedicion = false;
        segundaMedicionECHecha = false;
        segundaMedicionPHHecha = false;
      }
      // --- Control de iluminación (enciende 1h después de inicio del ciclo) ---
      if (millis() - tiempoInicioLuz >= 3600000UL && millis() - tiempoInicioLuz <= 3600000UL + INTERVALO_LUZ_ENCENDIDA) {
        estadoIlum = true;
      } else {
        estadoIlum = false;
      }

      if (data.humidity >= 50) {
        estadoVent = true;
      } else {
        estadoVent = false;
      }


      if (cicloActivo) { //Ciclo de recirculacion bomba y ajuste pH-EC
        if (tiempoActual - inicioCicloMillis <= duracionBomba) {
          // Mientras dure el ciclo de 2 horas
          lectura_sensores();  // Gestiona el relay de sensores

          if (!ecListo) {
            sensor_ph = false; // Apaga PH, prende EC
            lecturaTDS();      // Lee EC
            ajuste_ec();       // Ajuste de EC
            if (aviso_medicion_ph) {
              ecListo = true;
              estadoServo = true;
              aviso_medicion_ph = false;
              esperaPHIniciada = true;
              tiempoEsperaPH = millis(); // comienza espera de estabilización de pH
              sensor_ph = true;  // Apaga EC, prende PH
              lecturapH();       // Lee PH
              Serial.println("EC bien");
            }
          } 
          else if (!phListo) {
            if (esperaPHIniciada && millis() - tiempoEsperaPH >= 120000UL) { // 2 minutos de espera
              ajuste_pH();       // Ajuste de PH

              if (aviso_ph_fin) {
                phListo = true;
                aviso_ph_fin = false;
                estadoServo = false;
                // Preparar segunda medición
                enEsperaSegundaMedicion = true;
                tiempoEsperaSegundaMedicion = millis();
                segundaMedicionECHecha = false;
                segundaMedicionPHHecha = false;
                segundaMedicionHecha = false;
                sensor_ph = false;
                Serial.println("pH bien");
                // ⚠️ REINICIO DE VARIABLES DEL AJUSTE EC
                reiniciar_sensores();
              }
            }
          }
          else if (enEsperaSegundaMedicion && !segundaMedicionHecha) {
            // Esperar 30 minutos antes de segunda medición EC
            if (!segundaMedicionECHecha && millis() - tiempoEsperaSegundaMedicion >= 1800000UL) { // 30 minutos
              sensor_ph = false; // Apaga PH, prende EC
              lecturaTDS();      // Lee EC
              ajuste_ec();       // Ajuste de EC
              if (aviso_medicion_ph) {
                aviso_medicion_ph = false;
                estadoServo = true;
                esperaPHIniciada = true;
                tiempoEsperaPH = millis();
                sensor_ph = true; // Apaga EC, prende PH
                lecturapH();
                Serial.println("Lectura de pH iniciada");
                segundaMedicionECHecha = true;
              }
            }
            // Esperar 2 minutos para estabilizar pH antes de ajustar
            if (segundaMedicionECHecha && !segundaMedicionPHHecha && esperaPHIniciada && millis() - tiempoEsperaPH >= 120000UL) {
              ajuste_pH();

              if (aviso_ph_fin) {
                sensor_ph = false;
                estadoServo = false;
                aviso_ph_fin = false;
                segundaMedicionPHHecha = true;
                segundaMedicionHecha = true;
                Serial.println("Segunda medición: pH completada");
              }
            }
          }
        } else {
          // Fin del ciclo de 2 horas
          estadoBomba = false;
          estadoServo = false;
          cicloActivo = false;
        }
      }
      // Conteo de días cada 24 hs
      if (millis() - tiempo_dia_anterior >= INTERVALO_DIA) {
        dias_transcurridos++;
        tiempo_dia_anterior = millis();
        tiempoInicioLuz = millis(); // Reiniciar ciclo de iluminación
      }
    } else {
      // Programa finalizado
      inicio_programa = false;
      estadoBomba = false;
      estadoServo = false;
      estadoIlum = false;
      estadoVent = false;
      estadoEv1 = false;
      estadoEv2 = false;
      estadoEv3 = false;
    }
    
  }

  if(digitalRead(menu_config) == HIGH && millis() - lastDebounceTime >= tiempoDebounce){// Cambia el estado del menú
    menu++;
    lastDebounceTime = millis();
    if(menu==6){
      menu=0;
    }
  }
  if(menu==0){ //PRIMER PANTALLA: Principal
    if(digitalRead(menu_ok)==HIGH && millis() - lastDebounceTime >= tiempoDebounce){ //pulsador
      menu3++;
      lastDebounceTime = millis();
      if(menu3==6){
        menu3=0;
      }
    }
    if(menu3==0){//config etapa
      display.setCursor(1,32);
      display.print(">");
      if(digitalRead(menu_up)==HIGH && etapa < 11 && millis() - lastDebounceTime >= tiempoDebounce){ //se puede configurar hasta 10 etapas
        etapa++;
        lastDebounceTime = millis();
      }
      if(digitalRead(menu_down)==HIGH && etapa > 1 && millis() - lastDebounceTime >= tiempoDebounce){
        etapa--;
        lastDebounceTime = millis();
      }
    }
    if(menu3==1){//config dias
    display.setCursor(60,32);
    display.print(">");
      if(digitalRead(menu_up)==HIGH && dia_obj < 30 && millis() - lastDebounceTime >= tiempoDebounce){ //se puede configurar hasta 30 días
        dia_obj++;
        lastDebounceTime = millis();
      }
      if(digitalRead(menu_down)==HIGH && dia_obj > 1 && millis() - lastDebounceTime >= tiempoDebounce){
        dia_obj--;
        lastDebounceTime = millis();
      }
    }
    if(menu3==2){ //Seteo pH mínimo
      display.setCursor(1,42);
      display.print(">");
      if(digitalRead(menu_up)==HIGH && ph_min < 6 && millis() - lastDebounceTime >= tiempoDebounce){
        ph_min += 0.5;
        lastDebounceTime = millis();
      }
      if(digitalRead(menu_down)==HIGH && ph_min > 4 && millis() - lastDebounceTime >= tiempoDebounce){
        ph_min -= 0.5;
        lastDebounceTime = millis();
      }
    }
    if(menu3==3){ //Seteo de pH máximo
      display.setCursor(69,42);
      display.print(">");
      if(digitalRead(menu_up)==HIGH && ph_max < 8 && millis() - lastDebounceTime >= tiempoDebounce){
        ph_max += 0.5;
        lastDebounceTime = millis();
      }
      if(digitalRead(menu_down)==HIGH && ph_max > 6 && millis() - lastDebounceTime >= tiempoDebounce){
        ph_max -= 0.5;
        lastDebounceTime = millis();
      }
    }
    if(menu3==4){ //Seteo de EC minimo
      display.setCursor(1,52);
      display.print(">");
      if(digitalRead(menu_up)==HIGH && ec_min < 800 && millis() - lastDebounceTime >= tiempoDebounce){
        ec_min += 50;
        lastDebounceTime = millis();
      }
      if(digitalRead(menu_down)==HIGH && ec_min > 500 && millis() - lastDebounceTime >= tiempoDebounce){
        ec_min -= 50;
        lastDebounceTime = millis();
      }
    }
    if(menu3==5){ //Seteo de EC máximo
      display.setCursor(69,52);
      display.print(">");
      display.print(">");
      if(digitalRead(menu_up)==HIGH && ec_max < 1500 && millis() - lastDebounceTime >= tiempoDebounce){
        ec_max += 50;
        lastDebounceTime = millis();
      }
      if(digitalRead(menu_down)==HIGH && ec_max > 600 && millis() - lastDebounceTime >= tiempoDebounce){
        ec_max -= 50;
        lastDebounceTime = millis();
      }
    }
    display.setTextSize(1);           
    display.setTextColor(SSD1306_WHITE);
    display.drawRect(0, 0, 127, 63, WHITE);
    display.fillRect(0, 0, 127, 11, WHITE);
    display.drawLine(0, 30, 127, 30, WHITE);
    display.setTextColor(BLACK, WHITE);           
    display.setCursor(10, 2); 
    display.print("PANTALLA PRINCIPAL");
    display.setTextColor(WHITE, BLACK);
    display.setCursor(2,12); 
    display.print("Temp batea:");
    display.setCursor(80,12);
    display.print(String(temperatureC,0)+" C");
    display.setCursor(2,22);
    display.print("Volumen:");
    display.setCursor(80,22);
    if(digitalRead(NIVEL)==HIGH){
      display.print("Bien");
    }else{
      display.print("Llenar");
    }
    display.setCursor(7,32);
    display.print("Etapa:"+String(etapa));
    display.setCursor(75,32);
    display.print("Dias:"+String(dia_obj));
    display.setCursor(7,42);
    display.print("pHm:"+String(ph_min));
    display.setCursor(75,42);
    display.print("pHM:"+String(ph_max));
    display.setCursor(7,52);
    display.print("ECm:"+String(ec_min));
    display.setCursor(75,52);
    display.print("ECM:"+String(ec_max));
  }//Primer Pantalla
  if(menu==1){ //SEGUNDA PANTALLA: Lectura DHT22
    display.setTextSize(1);
    display.drawRect(0, 0, 127, 63, WHITE);
    display.fillRect(0, 0, 127, 11, WHITE);
    display.fillRect(0, 30, 127, 11, WHITE);
    display.setTextColor(BLACK, WHITE);
    display.setCursor(10,2);
    display.print("TEMPERATURA CABINA");
    display.setCursor(25,32);
    display.setTextColor(BLACK, WHITE);
    display.print("HUMEDAD CABINA");
    display.setTextColor(WHITE, BLACK);
    display.setCursor(50,14);
    display.setTextSize(2);
    display.print(String(data.temperature,0)+" C");
    display.setCursor(50,44);
    display.print(String(data.humidity,0)+"%");
  }
  if(menu==2){ //TERCER PANTALLA: Lectura TDS
    display.setTextSize(1);
    display.drawRect(0, 0, 127, 63, WHITE);
    display.fillRect(0, 0, 127, 11, WHITE);
    display.fillRect(0, 30, 127, 11, WHITE);
    display.setTextColor(BLACK, WHITE);
    display.setCursor(30,2);
    display.print("Medicion EC");
    display.setTextColor(WHITE, BLACK);
    display.setCursor(2,14);
    display.setTextSize(2);
    display.print("'OK' medir");
    display.setCursor(40,44);
    display.print(String(tdsValue,0));
    display.setTextSize(1);
    if(digitalRead(menu_ok)==HIGH && millis() - lastDebounceTime >= tiempoDebounce){
        sensor_ph=false;
        lastDebounceTime = millis();
    }
  }
  if(menu==3){ //TERCER PANTALLA: Lectura pH
    display.setTextSize(1);
    display.drawRect(0, 0, 127, 63, WHITE);
    display.fillRect(0, 0, 127, 11, WHITE);
    display.fillRect(0, 30, 127, 11, WHITE);
    display.setTextColor(BLACK, WHITE);
    display.setCursor(30,2);
    display.print("Medicion pH");
    display.setTextColor(WHITE, BLACK);
    display.setCursor(2,14);
    display.setTextSize(2);
    display.print("'OK' medir");
    display.setCursor(40,44);
    display.print(String(pH));
    display.setTextSize(1);
    if(digitalRead(menu_ok)==HIGH && millis() - lastDebounceTime >= tiempoDebounce){
        estadoServo = !estadoServo;
        sensor_ph=true;
        lastDebounceTime = millis();
    }
  }
  if(menu==4){ //CUARTA PANTALLA: Control manual salidas
    if (digitalRead(menu_up)==HIGH && menu2 < 5 && millis() - lastDebounceTime >= tiempoDebounce){
      menu2++;
      lastDebounceTime = millis();
    }
    if (digitalRead(menu_down)==HIGH && menu2 > 0 && millis() - lastDebounceTime >= tiempoDebounce){
      menu2--;
      lastDebounceTime = millis();
    }
    if (menu2==0){
      display.setCursor(1,15);
      display.print(">");
      if(digitalRead(menu_ok)==HIGH && millis() - lastDebounceTime >= tiempoDebounce){
        estadoVent = !estadoVent;
        lastDebounceTime = millis();
      }
    }
    if (menu2==1){
      display.setCursor(1,30);
      display.print(">");
      if(digitalRead(menu_ok)==HIGH && millis() - lastDebounceTime >= tiempoDebounce){
        estadoIlum = !estadoIlum;
        lastDebounceTime = millis();
      }
    }
    if (menu2==2){
      display.setCursor(1,45);
      display.print(">");
      if(digitalRead(menu_ok)==HIGH && millis() - lastDebounceTime >= tiempoDebounce){
        estadoBomba = !estadoBomba;
        lastDebounceTime = millis();
      }
    }
    if (menu2==3){
      display.setCursor(73,15);
      display.print(">");
      if(digitalRead(menu_ok)==HIGH && millis() - lastDebounceTime >= tiempoDebounce){
        estadoEv1 = !estadoEv1;
        lastDebounceTime = millis();
      }
    }
    if (menu2==4){
      display.setCursor(73,30);
      display.print(">");
      if(digitalRead(menu_ok)==HIGH && millis() - lastDebounceTime >= tiempoDebounce){
        estadoEv2 = !estadoEv2;
        lastDebounceTime = millis();
      }
    }
    if (menu2==5){
      display.setCursor(73,45);
      display.print(">");
      if(digitalRead(menu_ok)==HIGH && millis() - lastDebounceTime >= tiempoDebounce){
        estadoEv3 = !estadoEv3;
        lastDebounceTime = millis();
      }
    }
    display.setTextSize(1);
    display.drawRect(0, 0, 127, 63, WHITE);
    display.fillRect(0, 0, 127, 11, WHITE);
    display.setTextColor(BLACK, WHITE);           
    display.setCursor(25, 2); 
    display.print("CONTROL MANUAL");
    display.setTextColor(WHITE, BLACK);
    display.setCursor(8,15); 
    display.print("VENT.");
    display.setCursor(44,15);
    if(estadoVent==false){
      display.print("OFF");
    }else{
      display.print("ON");
    }
    display.setCursor(8,30);
    display.print("ILUM.");
    display.setCursor(44,30);
    if(estadoIlum==false){
      display.print("OFF");
    }else{
      display.print("ON");
    }
    display.setCursor(8,45);
    display.print("BOMBA");
    display.setCursor(44,45);
    if(estadoBomba==false){
      display.print("OFF");
    }else{
      display.print("ON");
    }
    display.setCursor(80,15);
    display.print("EV1");
    display.setCursor(105,15);
    if(estadoEv1==false){
      display.print("OFF");
    }else{
      display.print("ON");
    }
    display.setCursor(80,30);
    display.print("EV2");
    display.setCursor(105,30);
    if(estadoEv2==false){
      display.print("OFF");
    }else{
      display.print("ON");
    }
    display.setCursor(80,45);
    display.print("EV3");
    display.setCursor(105,45);
    if(estadoEv3==false){
      display.print("OFF");
    }else{
      display.print("ON");
    }
  }
   if(menu==5){
    display.setTextSize(1);           
    display.setTextColor(SSD1306_WHITE);
    display.drawRect(0, 0, 127, 63, WHITE);
    display.fillRect(0, 0, 127, 11, WHITE);
    display.setTextColor(BLACK, WHITE);           
    display.setCursor(15, 2); 
    display.print("INICIO PROGRAMA");
    display.setTextColor(WHITE, BLACK);
    display.setCursor(2,12);
    display.print("Dias transc. "+String(dias_transcurridos));
    display.setCursor(2,22);
    display.print("Freq recirc. 12hs");
    display.setCursor(2,32);
    display.print("Duracion recirc. 2hs");
    display.setCursor(2,42);
    display.print("Iluminacion 16hs");
    if(digitalRead(menu_ok)==HIGH && millis() - lastDebounceTime >= tiempoDebounce){
      inicio_programa = true;
      lastDebounceTime = millis();
    }
    if (digitalRead(menu_ok)==HIGH && millis() - lastDebounceTime >= tiempoDebounce && inicio_programa==true){// presionar para apagar
    inicio_programa = false;
    estadoBomba = false;
    estadoServo = false;
    estadoIlum = false;
    estadoVent = false;
    estadoEv1 = false;
    estadoEv2 = false;
    estadoEv3 = false;
    }
  }
  display.display();
  esp_task_wdt_reset();  // Alimentar el watchdog
  delay(10);  // importante mantener fluidez del loop
}
//FUNCIONES
void lecturaTDS(){
  float factorCalibracion = 718.0 / 524.0; // ~1.37 Calibración de ecuacion segun medicion
  static unsigned long analogSampleTimepoint = millis();
  if(millis()-analogSampleTimepoint > 40U){     //every 40 milliseconds,read the analog value from the ADC
    analogSampleTimepoint = millis();
    delayMicroseconds(20);
    analogBuffer[analogBufferIndex] = analogRead(TdsSensorPin);    //read the analog value and store into the buffer
    analogBufferIndex++;
    if(analogBufferIndex == SCOUNT){ 
      analogBufferIndex = 0;
    }
  }   
  static unsigned long printTimepoint = millis();
  if(millis()-printTimepoint > 800U){
    printTimepoint = millis();
    for(copyIndex=0; copyIndex<SCOUNT; copyIndex++){
      analogBufferTemp[copyIndex] = analogBuffer[copyIndex];
      // read the analog value more stable by the median filtering algorithm, and convert to voltage value
      averageVoltage = getMedianNum(analogBufferTemp,SCOUNT) * (float)VREF / 4096.0;
      //temperature compensation formula: fFinalResult(25^C) = fFinalResult(current)/(1.0+0.02*(fTP-25.0)); 
      float compensationCoefficient = 1.0+0.02*(temperature-25.0);
      //temperature compensation
      float compensationVoltage=averageVoltage/compensationCoefficient;
      //convert voltage value to tds value
      tdsValue=(133.42*compensationVoltage*compensationVoltage*compensationVoltage - 255.86*compensationVoltage*compensationVoltage + 857.39*compensationVoltage)*0.5;
      tdsValue *= factorCalibracion;
    }
  }
  esp_task_wdt_reset();
}
void lecturaTemperatura(){ //Sensor temperatura agua
  if (!esperandoTemperatura && millis() - ultimaLecturaTemp > 5000) {  // cada 5 s
    sensors.requestTemperatures();  // solo inicia
    ultimaLecturaTemp = millis();
    esperandoTemperatura = true;
  }
  if (esperandoTemperatura && millis() - ultimaLecturaTemp >= 750) {
    temperatureC = sensors.getTempCByIndex(0);
    esperandoTemperatura = false;
  }
}
void lecturapH() {
  static unsigned long sampleTimer = 0;
  static unsigned long printTimer = 0;
  if (millis() - sampleTimer > 40) {
    sampleTimer = millis();
    delayMicroseconds(20);
    int lecturaReal = analogRead(pHpin);
    pHBuffer[pHIndex++] = lecturaReal;
    if (pHIndex >= pH_SAMPLES) pHIndex = 0;
  }
  if (millis() - printTimer > 800) {
    printTimer = millis();
    for (int i = 0; i < pH_SAMPLES; i++) {
      pHBufferTemp[i] = pHBuffer[i];
    }
    float voltaje = calcularMediana(pHBufferTemp, pH_SAMPLES) * VREF / 4095.0;
    pH = slope * voltaje + offset;
  }
  esp_task_wdt_reset();
}
void relay_vent(){ //Salida ventilador
  if(estadoVent==false){
    digitalWrite(VENTILACION, HIGH);
  }else{
    digitalWrite(VENTILACION, LOW);
  }
}
void relay_ilum(){ //Salida iluminación
  if(estadoIlum==false){
    digitalWrite(ILUMINACION, HIGH);
  }else{
    digitalWrite(ILUMINACION, LOW);
  }
}
void relay_bomba(){ //Salida bomba
  if(estadoBomba==false){
    digitalWrite(BOMBA, HIGH);
  }else{
    digitalWrite(BOMBA, LOW);
  }
}
void relay_ev1(){ //Salida Electroválvula 1
  if(estadoEv1==false){
    digitalWrite(EV1, HIGH);
  }else{
    digitalWrite(EV1, LOW);
  }
}
void relay_ev2(){ //Salida Electroválvula 2
  if(estadoEv2==false){
    digitalWrite(EV2, HIGH);
  }else{
    digitalWrite(EV2, LOW);
  }
}
void relay_ev3(){ //Salida Electroválvula 3
  if(estadoEv3==false){
    digitalWrite(EV3, HIGH);
  }else{
    digitalWrite(EV3, LOW);
  }
}
void servo_sensor(){ //Movimiento de servo para sensores
  if(estadoServo==false){
    miServo.write(0);
  }else{
    miServo.write(90);
  }
}
void lectura_sensores(){ //Movimiento de servo para sensores
  if(sensor_ph==false){
    digitalWrite(activar_sensores, HIGH); //Apaga ph para medir ec
  }else{
    digitalWrite(activar_sensores, LOW); //Apaga ec para medir ph
  }
}
void ajuste_pH() {
  unsigned long tiempoActual1 = millis();
  if (lecturasCorrectas >= 3) {//Si despues de medir 3 veces bien el ph, sale de la funcion
    aviso_ph_fin = true;
    lecturasCorrectas = 0;
    return;
  }
  if (inyectando && (tiempoActual1 - inicioInyeccion >= 1000)) {// Inyecta tras 1 segundo
    estadoEv1 = false;
    estadoEv2 = false;
    inyectando = false;
    esperando = true;
    ultimaEjecucion = millis();
    return;
  }
  if (esperando && (tiempoActual1 - ultimaEjecucion < 120000)) { // Espera 2 min entre inyección, para que se estabilice bien la medicion
    return;
  } else if (esperando) {
    esperando = false;
  }
  if (!inyectando && !esperando) {
    if (pH > ph_max) {
      estadoEv1 = true;
      inicioInyeccion = millis();
      inyectando = true;
      lecturasCorrectas = 0; // Reiniciar contador si está fuera del rango
    } 
    if (pH < ph_min) {
      estadoEv2 = true;
      inicioInyeccion = millis();
      inyectando = true;
      lecturasCorrectas = 0; // Reiniciar contador
    }
    if(pH > ph_min && pH < ph_max){
      lecturasCorrectas++; // Sumamos una lectura correcta
      ultimaEjecucion = millis();
      esperando = true;
    }
  }
  esp_task_wdt_reset();
}
void ajuste_ec() {
  unsigned long tiempoActual11 = millis();
  if (lecturasCorrectas1 >= 3) {
    aviso_medicion_ph = true;
    estadoEv3 = false;
    lecturasCorrectas1 = 0;
    return;
  }
  // Fin de inyección tras 1 segundo
  if (inyectando1 && (tiempoActual11 - inicioInyeccion1 >= 1000)) {
    estadoEv3 = false;
    inyectando1 = false;
    esperando1 = true;
    ultimaEjecucion1 = millis();
    return;
  }
  // Espera de 60 segundos entre inyecciones
  if (esperando1 && (tiempoActual11 - ultimaEjecucion1 < 60000)) {
    return;
  } else if (esperando1) {
    esperando1 = false;
  }
  // Medición y ajuste
  if (!inyectando1 && !esperando1) {
    if (tdsValue < ec_min) {
      estadoEv3 = true;
      inicioInyeccion1 = millis();
      inyectando1 = true;
      lecturasCorrectas1 = 0;
    }
    else if (tdsValue >= ec_min && tdsValue < ec_max) {
      estadoEv3 = false;  // ¡Muy importante!
      lecturasCorrectas1++;
      ultimaEjecucion1 = millis();
      esperando1 = true;
    }
    else if (tdsValue >= ec_max) {
      estadoEv3 = false;  // En caso que se haya pasado por demás
      lecturasCorrectas1 = 0;
      esperando1 = true;
      ultimaEjecucion1 = millis();
    }
  }
  esp_task_wdt_reset();  // Alimentar watchdog
}
void reiniciar_sensores() { //Funcion para reiniciar variables de sensores en segunda medición
  ultimaEjecucion1 = 0;
  inicioInyeccion1 = 0;
  inyectando1 = false;
  esperando1 = false;
  lecturasCorrectas1 = 0;
  ultimaEjecucion = 0;
  inicioInyeccion = 0;
  inyectando = false;
  esperando = false;
  lecturasCorrectas = 0;
  estadoEv1 = false;
  estadoEv2 = false;
  estadoEv3 = false;
}