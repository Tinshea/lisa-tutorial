# Domaines Abstraits pour l'Analyse Statique avec LiSA

Ce projet implémente trois domaines abstraits pour l'analyse statique de programmes avec la bibliothèque LiSA (Library for Static Analysis).

## Auteurs
- Malek BOUZARKOUNA — 28706508
- Yacine KESSAL — 21311739

---

# 1. SetOfFloatValuesWithOverflow

Ce domaine abstrait représente des ensembles de valeurs flottantes avec **cardinalité limitée** et **détection automatique des débordements**, améliorant ainsi la sûreté des analyses numériques.

## Structure

Cette classe implémente `BaseNonRelationalValueDomain<SetOfFloatValuesWithOverflow>` et maintient un ensemble borné de valeurs flottantes:

```java
private final int maxNumberOfElements;
private final Set<Float> values;

public static final SetOfFloatValuesWithOverflow TOP = new SetOfFloatValuesWithOverflow((Set<Float>) null);
public static final SetOfFloatValuesWithOverflow BOTTOM = new SetOfFloatValuesWithOverflow(new HashSet<>());
```

---

## Fonctionnalités Implémentées

### 1. Gestion des Opérations Binaires

La méthode `evalBinaryExpression` prend en charge toutes les opérations arithmétiques avec détection des débordements:

| Opération | Comportement |
|-----------|-------------|
| Addition (`+`) | Détection des résultats `Infinity` ou `NaN` → TOP |
| Soustraction (`-`) | Vérification des valeurs hors limites → TOP |
| Multiplication (`*`) | Vérification des produits causant des overflows → TOP |
| Division (`/`) | Division par zéro → BOTTOM, résultats infinis → TOP |

```java
@Override
public SetOfFloatValuesWithOverflow evalBinaryExpression(
        BinaryOperator operator, 
        SetOfFloatValuesWithOverflow left, 
        SetOfFloatValuesWithOverflow right, 
        ProgramPoint pp, 
        SemanticOracle oracle) throws SemanticException {
    
    if (left.isTop() || right.isTop())
        return TOP;
    if (left.isBottom() || right.isBottom())
        return BOTTOM;
    
    Set<Float> result = new HashSet<>();
    
    if (operator instanceof AdditionOperator) {
        // Traitement de l'addition avec détection d'overflow
        // ...
    } else if (operator instanceof DivisionOperator) {
        // Détection spéciale de division par zéro
        // ...
    }
    
    return result.size() > maxNumberOfElements ? TOP : new SetOfFloatValuesWithOverflow(result);
}
```

---

### 2. Satisfiabilité des Conditions

La méthode `satisfiesBinaryExpression` détermine si des conditions sont satisfaites:

```java
@Override
public Satisfiability satisfiesBinaryExpression(
        BinaryOperator operator, 
        SetOfFloatValuesWithOverflow left, 
        SetOfFloatValuesWithOverflow right, 
        ProgramPoint pp, 
        SemanticOracle oracle) throws SemanticException {
    
    if (left.isTop() || right.isTop())
        return Satisfiability.UNKNOWN;
    
    if (operator instanceof ComparisonLt) {
        for (Float i : left.values)
            for (Float j : right.values)
                if (!(i < j))
                    return Satisfiability.UNKNOWN;
        return Satisfiability.SATISFIED;
    }
    
    return BaseNonRelationalValueDomain.super.satisfiesBinaryExpression(operator, left, right, pp, oracle);
}
```

Cette implémentation permet de:
- Vérifier si toutes les combinaisons possibles de valeurs satisfont une condition
- Garantir la correction de l'analyse en retournant `UNKNOWN` en cas de doute

---

### 3. Raffinement d'Environnement

La méthode `assumeBinaryExpression` filtre les valeurs qui ne satisfont pas une condition:

```java
@Override
public ValueEnvironment<SetOfFloatValuesWithOverflow> assumeBinaryExpression(
        ValueEnvironment<SetOfFloatValuesWithOverflow> environment, 
        BinaryOperator operator, 
        ValueExpression left, 
        ValueExpression right,
        ProgramPoint src, 
        ProgramPoint dest, 
        SemanticOracle oracle) throws SemanticException {
    
    if (operator instanceof ComparisonLt && left instanceof Variable && right instanceof Constant) {
        Variable x = (Variable) left;
        Constant y = (Constant) right;
        
        if (y.getValue() instanceof Float) {
            SetOfFloatValuesWithOverflow vals = environment.getState(x);
            if (vals.isTop())
                return environment;
            
            Set<Float> filtered = new HashSet<>();
            for (Float v : vals.values)
                if (v < (Float) y.getValue())
                    filtered.add(v);
                    
            environment.putState(x, new SetOfFloatValuesWithOverflow(filtered));
            return environment;
        }
    }
    
    return BaseNonRelationalValueDomain.super.assumeBinaryExpression(
            environment, operator, left, right, src, dest, oracle);
}
```

Cela permet d'affiner progressivement l'analyse en fonction des branches conditionnelles du programme.

---

### 4. Gestion du Treillis Abstrait

Cette implémentation inclut toutes les opérations de treillis nécessaires:

- **Borne supérieure (`lubAux`)**: Fusionne des ensembles avec gestion de la cardinalité maximale
- **Comparaison d'ordre (`lessOrEqualAux`)**: Vérification d'inclusion entre ensembles
- **Constantes**: Conversion des constantes flottantes en éléments du domaine

---

## Exemple d'Utilisation

Prenons un exemple de programme qui présente des risques d'overflow:

```imp
def a = 1000000000.0;       // 10^9
def b = a * a;              // 10^18
def c = b * b;              // 10^36
def d = c * c;              // 10^72 (overflow)
```

Le domaine détectera automatiquement le débordement à l'opération finale et établira `d = TOP` (valeur inconnue), évitant ainsi la propagation de résultats incorrects.

---

## Limites et Considérations

- Précision réduite quand le nombre de valeurs distinctes dépasse `maxNumberOfElements`
- Passage au TOP (sur-approximation) en cas d'opérations transcendantales non supportées
- Perte de précision relationnelle car le domaine est non-relationnel

---

# 2. TwoVarLinearInequality

Ce domaine relationnel implémente l'analyse d'inégalités linéaires impliquant **au plus deux variables** par contrainte, permettant de représenter des relations de la forme `a*x + b*y <= c`.

## Structure

Cette classe implémente `ValueDomain<TwoVarLinearInequality>` et maintient un ensemble d'inégalités linéaires:

```java
public class TwoVarLinearInequality implements ValueDomain<TwoVarLinearInequality> {
    private final boolean isTop;
    private final Set<Inequality> inequalities;
    
    // Classe interne représentant une inégalité linéaire
    public static class Inequality {
        private final int a, b, c;
        private final Identifier x, y;
        private final boolean isProtected;
        // ...
    }
    // ...
}
```

Chaque inégalité est de la forme `a*x + b*y <= c`, où `a` et `b` sont des coefficients entiers, `x` et `y` sont des identifiants (variables) ou null, et `c` est une constante entière.

---

## Fonctionnalités Implémentées

### 1. Clôture Transitive des Inégalités

Le domaine implémente un mécanisme de clôture transitive qui combine les inégalités pour en déduire de nouvelles:

```java
private void applyCompletion() {
    // ...
    do {
        changed = false;
        Set<Inequality> toAdd = new HashSet<>();
        for (Inequality i1 : completed) {
            for (Inequality i2 : completed) {
                if (i1.canCombineWith(i2)) {
                    Inequality derived = i1.combine(i2);
                    if (derived != null && !completed.contains(derived)) {
                        // Ajoute la nouvelle inégalité dérivée
                        // ...
                    }
                }
            }
        }
        completed.addAll(toAdd);
        iteration++;
    } while (changed && iteration < maxIterations && completed.size() < maxInequalities);
    // ...
}
```

Cette méthode permet de déduire de nouvelles relations entre variables en combinant les contraintes existantes, améliorant la précision de l'analyse.

---

### 2. Assignations Avancées

La méthode `assign` gère plusieurs formes d'affectations et met à jour les inégalités en conséquence:

- **Affectation de constantes**: `x = 5`
- **Affectation d'identifiants**: `x = y`
- **Expressions linéaires**: `x = y + 10`
- **Expressions plus complexes**: `x = 2*y + 5`

```java
@Override
public TwoVarLinearInequality assign(Identifier id, ValueExpression expression, ProgramPoint pp, SemanticOracle oracle)
        throws SemanticException {
    if (isBottom() || isHeapRelated(id)) return this;

    Set<Inequality> updated = removeIdentifier(id).inequalities;
    
    if (expression instanceof Constant) {
        // Affectation d'une constante
    } else if (expression instanceof Identifier) {
        // Affectation d'un identifiant
    } else if (expression instanceof BinaryExpression) {
        // Traitement d'expressions binaires
        // ...
    }
    
    return isSatisfiable(updated) ? new TwoVarLinearInequality(updated) : BOTTOM;
}
```

Cette implémentation permet de suivre précisément les relations linéaires entre variables tout au long de l'exécution du programme.

---

### 3. Analyse des Conditions

La méthode `assume` permet d'affiner l'état du domaine à partir des conditions rencontrées dans le programme:

```java
@Override
public TwoVarLinearInequality assume(ValueExpression expression, ProgramPoint src, ProgramPoint dest, SemanticOracle oracle)
        throws SemanticException {
    if (isBottom()) return this;

    Set<Inequality> updated = new HashSet<>(inequalities);
    if (expression instanceof BinaryExpression) {
        BinaryExpression bin = (BinaryExpression) expression;
        if (bin.getOperator() instanceof ComparisonLe) {
            if (bin.getLeft() instanceof Identifier && bin.getRight() instanceof Identifier) {
                // x <= y
                // ...
            } else if (bin.getLeft() instanceof Identifier && bin.getRight() instanceof BinaryExpression) {
                // x <= y + c
                // ...
            }
        }
    }
    return isSatisfiable(updated) ? new TwoVarLinearInequality(updated) : BOTTOM;
}
```

Cette méthode traite principalement les inégalités de la forme `x <= y` ou `x <= y + c`, les transformant en contraintes internes.

---

### 4. Contrôle de l'Explosion Combinatoire

Le domaine incorpore plusieurs mécanismes pour éviter l'explosion combinatoire des inégalités:

- **Limite d'itérations** dans la clôture transitive
- **Limite du nombre d'inégalités** stockées
- **Élimination des inégalités redondantes**
- **Gestion des coefficients** limités aux valeurs 1, -1, 0

```java
private Set<Inequality> removeRedundant(Set<Inequality> set) {
    Map<String, Inequality> tightened = new HashMap<>();
    // ...
    for (Inequality ineq : set) {
        if (ineq.isTrivial() || ineq.isProtected) continue;
        String key = ineq.getKey();
        tightened.compute(key, (k, old) -> {
            if (old == null) return ineq;
            return old.c > ineq.c ? ineq : old;
        });
    }
    // ...
    return result;
}
```

Ces mécanismes garantissent la terminaison de l'analyse tout en préservant la précision pour les cas les plus courants.

---

## Avantages

- **Relationnel**: Capture des relations précises entre variables (comme `x <= y + 10`)
- **Propagation transitive**: Déduit de nouvelles inégalités par combinaison des existantes
- **Affectations complexes**: Gère les expressions linéaires composées
- **Contrôle de complexité**: Mécanismes pour éviter l'explosion combinatoire des contraintes

---

## Limites

- Inégalités limitées à deux variables maximum
- Coefficients des variables limités à {-1, 0, 1} pour contrôler la complexité
- Ne gère que les inégalités de la forme `<=` (et non les égalités strictes)
- Nombre maximal d'inégalités et d'itérations fixé pour garantir la terminaison

---

# 3. TwoVarInequalityAndFloatCartesian

Ce domaine composite combine les deux domaines précédents en un **produit cartésien**, bénéficiant ainsi des avantages des deux approches simultanément.

## Structure

```java
public class TwoVarInequalityAndFloatCartesian
        extends CartesianProduct<
        TwoVarInequalityAndFloatCartesian,
        TwoVarLinearInequality,
        ValueEnvironment<SetOfFloatValuesWithOverflow>,
        ValueExpression,
        Identifier>
        implements ValueDomain<TwoVarInequalityAndFloatCartesian> {
    // ...
}
```

Ce produit cartésien combine:
1. **TwoVarLinearInequality**: Pour capturer les relations linéaires entre variables
2. **ValueEnvironment<SetOfFloatValuesWithOverflow>**: Pour suivre précisément les valeurs flottantes avec détection d'overflow

---

## Avantages de la Combinaison

- **Précision accrue**: Bénéficie simultanément des analyses relationnelle et non-relationnelle
- **Détection d'erreurs étendue**: Identifie à la fois les violations d'inégalités et les overflows
- **Complémentarité des approches**: Les domaines se renforcent mutuellement

Par exemple, cette combinaison peut analyser ce type de programme:

```imp
def x = 1.5;
def y = 10.0;
if (x < y) {
    x = x * 1000000000.0;  // Risque d'overflow
    y = y - x;             // Inégalité linéaire modifiée
}
```

L'analyse pourra:
1. Détecter si `x` risque un overflow lors de la multiplication
2. Suivre la relation d'inégalité entre `x` et `y` avant et après les opérations
3. Identifier les branches conditionnelles impossibles à atteindre

---

## Utilisation dans LiSA

Les domaines peuvent être configurés individuellement ou combinés dans une analyse LiSA comme suit:

```java
// Configuration pour SetOfFloatValuesWithOverflow seul
SetOfFloatValuesWithOverflow floatDomain = new SetOfFloatValuesWithOverflow(5);
conf.abstractState = DefaultConfiguration.simpleState(
        DefaultConfiguration.defaultHeapDomain(),
        new ValueEnvironment<>(floatDomain),
        DefaultConfiguration.defaultTypeDomain());

// Configuration pour TwoVarLinearInequality seul
conf.abstractState = new TwoVarLinearInequality();

// Configuration pour le produit cartésien
TwoVarLinearInequality ineqDomain = new TwoVarLinearInequality();
ValueEnvironment<SetOfFloatValuesWithOverflow> floatEnv = new ValueEnvironment<>(new SetOfFloatValuesWithOverflow(5));
conf.abstractState = new TwoVarInequalityAndFloatCartesian(ineqDomain, floatEnv);
```

Pour exécuter une analyse:

```java
// Parsing du code source
Program program = IMPFrontend.processFile("inputs/example.imp");

// Configuration de LiSA
LiSAConfiguration conf = new DefaultConfiguration();
conf.workdir = "outputs/analysis-results";
conf.analysisGraphs = GraphType.HTML;

// Exécution de l'analyse
LiSA lisa = new LiSA(conf);
lisa.run(program);
```

Cette configuration permet d'obtenir une analyse de programme plus précise et robuste, capable de détecter une gamme plus large d'erreurs potentielles.
