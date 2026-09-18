#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Bot de coleta de dados (web scraping) com notificacao no Telegram e/ou Discord.

COMO USAR (resumo — o passo a passo completo esta no README.md):

    python3 bot.py --testar      # testa se a notificacao esta configurada certa
    python3 bot.py               # roda a coleta UMA vez
    python3 bot.py --loop        # roda a cada 15 minutos, sem parar

Toda a configuracao sensivel (token do bot, id do grupo) vem do arquivo .env.
NADA de senha ou token fica escrito dentro deste arquivo.
"""

from __future__ import annotations   # compatibilidade com Python 3.9

import argparse
import html
import json
import logging
import os
import re
import sqlite3
import sys
import time
import urllib.robotparser
from datetime import datetime, timezone
from typing import Optional
from urllib.parse import urljoin, urlparse
from zoneinfo import ZoneInfo

import requests
from dotenv import load_dotenv
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry


# ==========================================================================
#  1. CONFIGURACAO DO SITE ALVO (cssdeals.com)
# ==========================================================================
#
#  IMPORTANTE — POR QUE NAO PRECISAMOS VARRER ABA POR ABA:
#
#  O site tem dezenas de abas (Shoes, Hoodie, Pants...) e cada uma tem
#  subabas de tamanho, com 20 produtos por pagina e as vezes 20+ paginas.
#  Varrer tudo isso daria centenas de requisicoes a cada rodada.
#
#  Nao e necessario. O site tem uma API interna que devolve os produtos
#  JA ORDENADOS DO MAIS NOVO PARA O MAIS ANTIGO, misturando todas as
#  categorias e tamanhos. Como voce so quer LANCAMENTOS NOVOS, basta ler
#  a primeira pagina dessa lista: o que apareceu de novo desde a ultima
#  vez esta sempre no topo.
#
#  Resultado: 1 requisicao a cada 15 minutos, em vez de centenas — e
#  mesmo assim nenhum lancamento escapa, de nenhuma categoria.
# ==========================================================================

SITE_BASE = "https://cssdeals.com"

# Endereco da lista de produtos (a API interna do proprio site)
API_PRODUTOS = SITE_BASE + "/api/product"

# Endereco dos detalhes de UM produto especifico — e aqui, e so aqui, que
# vem as fotos REAIS da pagina do produto (campo "images"), a variacao
# escolhida (cor/tamanho) e o link de origem. A lista (API_PRODUTOS) nao
# traz nada disso, so o titulo/preco/capa.
API_PRODUTO_DETALHE = SITE_BASE + "/api/product/{id}"

# Quantos produtos ler por rodada (do mais novo para o mais antigo).
# 50 da uma margem folgada: mesmo que o site cadastre varios produtos
# em 15 minutos, nenhum passa despercebido.
TAMANHO_PAGINA = 100          # maximo aceito pela API (acima disso ela devolve 20!)

# Paginas da leitura RAPIDA (a de cada ciclo normal, nao a profunda).
# Com 1 pagina so (100 produtos), lancamentos que entram mais pra baixo
# da lista nessa hora podem escapar por pouco. 2 paginas (200 produtos)
# da bem mais margem, ao custo de 1 requisicao a mais por ciclo.
PAGINAS_RAPIDAS = 2

# Quantas paginas buscar AO MESMO TEMPO (em paralelo), tanto na leitura
# rapida quanto na varredura profunda. Nao aumenta o numero de
# requisicoes — so evita que uma espere a outra terminar. Numa varredura
# de 10 paginas, por exemplo, o tempo total cai de ~15s (sequencial) para
# uns ~4s (paralelo), o que sai direto do seu atraso ate ser avisado.
PAGINAS_SIMULTANEAS = 4

# --- Varredura profunda ---
#  A API ordena por ID, que e a ordem de CRIACAO do produto — nao a de
#  publicacao. O cssdeals as vezes torna visivel um produto criado ha
#  dias: ele carrega o ID antigo e nasce no MEIO da lista, nunca no topo.
#
#  Ler so o topo deixaria esses produtos invisiveis para sempre, porque
#  eles nunca sobem. Por isso, de tempos em tempos o bot varre uma janela
#  bem mais funda procurando qualquer ID que ainda nao conheca,
#  independentemente da posicao.
PAGINAS_PROFUNDAS = 10        # 10 x 100 = 1000 produtos (~3 dias)
MINUTOS_ENTRE_VARREDURAS = 20
DELAY_ENTRE_PAGINAS = 1.5     # (sem uso no momento — as paginas agora vao em paralelo)

# Pagina do link de compra de cada produto
URL_PRODUTO = SITE_BASE + "/product-detail.html?itemid={id}"

# O servidor de imagens do CSSDeals (Aliyun OSS) sabe redimensionar pela
# propria URL, so acrescentando esse parametro no final. A foto original
# chega a ~3 MB; com isso cai pra ~80 KB — o Telegram BAIXA a imagem a
# cada envio, entao foto grande atrasa a entrega da mensagem.
REDIMENSIONA_FOTO = "?x-oss-process=image/resize,w_800/quality,Q_80"

# Link do botao "BUY NOW" do proprio site: manda direto pro carrinho do
# CSSBuy (o agente de compra por tras do CSSDeals). Montamos isso sem
# NENHUMA requisicao extra — so precisa do id do produto, que ja temos
# assim que o item e detectado.
URL_COMPRA = "https://www.cssbuy.com/waiting?type=cssdeals&productId={id}&quantity=1"

# Trecho extra colado no fim do link de compra — para o SEU codigo de
# indicacao do CSSBuy, caso tenha um (gera comissao quando alguem compra
# por esse link). Configure em CSSBUY_EXTRA no Railway/.env, exatamente
# como aparece no seu link de indicacao, por exemplo:
#     &promotecode=SEUCODIGO
# Deixe vazio (padrao) para nao acrescentar nada.
CSSBUY_EXTRA = os.getenv("CSSBUY_EXTRA", "").strip()

# Nome de cada plataforma de origem (vem no campo salePlatform)
PLATAFORMAS = {1: "Taobao", 2: "Weidian", 3: "1688"}

# Categorias do site — usado so para mostrar o nome na mensagem.
# (levantado de https://cssdeals.com/api/category/tree)
CATEGORIAS = {
    "11": "Shoes", "12": "Coat", "14": "T-shirts", "15": "Pants",
    "16": "Accessories", "18": "Fashion", "19": "Electronics",
    "20": "Watches", "21": "Cell phone", "22": "Earphone",
    "23": "Computer accessories", "24": "Audio & Video",
    "26": "Hat&Bags", "27": "Belt&Glasses", "30": "Gloves& Scarf",
    "31": "Underwear & Sleepwear", "32": "Hoodie", "33": "down jacket",
    "34": "suit", "35": "long sleeve", "36": "sports goods",
    "37": "toy", "38": "phone case", "39": "accessories",
    "40": "socks", "41": "Accessories", "43": "sports goods",
    "44": "perfume", "45": "suitcase",
}


# ==========================================================================
#  2. CONFIGURACOES GERAIS
# ==========================================================================
# (algumas podem ser ajustadas por variavel de ambiente, sem mexer no codigo)

BANCO_DADOS = "dados.db"          # arquivo SQLite onde tudo fica salvo
ARQUIVO_LOG = "bot.log"           # historico do que o bot fez

# --- Reestoque: produtos que esgotaram e voltaram a vender ---
# Depois de avisar um produto, ficamos de olho no estoque dele por um
# tempo. Se ele esgotar e depois voltar a ter estoque, avisamos de novo —
# e uma segunda chance de comprar o mesmo item.
REESTOQUE_MAX_ITENS = 300         # quantos produtos notificados ficam sob vigilancia
REESTOQUE_SIMULTANEAS = 6         # checagens de estoque em paralelo
# Segundos entre cada rodada no modo --loop (servidor sempre ligado).
# 60s da o menor atraso possivel sem pesar no site: e 1 consulta por
# minuto, enquanto o site publica ~2 produtos a cada 15 minutos.
# O valor real e lido do .env em carregar_config() — este e so o padrao.
INTERVALO_PADRAO = 60

# --- Janela de rastreio mais rapido ("pico") ---
# Entre JANELA_RAPIDA_INICIO e JANELA_RAPIDA_FIM (horario de Brasilia), o
# bot verifica o site a cada INTERVALO_RAPIDO_SEGUNDOS em vez do intervalo
# normal. Fora desse horario, continua no intervalo normal de sempre.
#
# Os tres valores dao pra ajustar via variavel de ambiente (Railway/.env),
# sem precisar mexer no codigo — ver JANELA_RAPIDA_INICIO/FIM/
# INTERVALO_RAPIDO_SEGUNDOS em carregar_config(). A janela pode atravessar
# a meia-noite (ex: 22:00 as 09:00) sem problema.
FUSO_HORARIO_JANELA = ZoneInfo("America/Sao_Paulo")
JANELA_RAPIDA_INICIO_PADRAO = "22:00"
JANELA_RAPIDA_FIM_PADRAO = "09:00"
INTERVALO_RAPIDO_PADRAO = 15
DELAY_ENTRE_REQUISICOES = 1.5     # (sem uso no momento — ver DELAY_ENTRE_PAGINAS)
DELAY_ENTRE_MENSAGENS = 1.2       # segundos entre mensagens (limite do Telegram)
TIMEOUT = 30                      # segundos ate desistir de uma requisicao
TIMEOUT_DETALHE = 6               # timeout CURTO para a busca de fotos reais —
                                   # se o site demorar, seguimos com a capa em
                                   # vez de travar o aviso esperando
MAX_TENTATIVAS = 3                # quantas vezes tentar de novo se der erro
MAX_NOTIFICACOES_POR_RODADA = 20  # trava de seguranca contra spam
MAX_IMAGENS_DISCORD = 4           # quantas fotos no maximo mostrar na galeria do Discord

# --- Traducao dos titulos ---
# Os titulos vem do site em chines e ingles. O bot traduz para portugues
# usando o MyMemory, que e gratuito e NAO precisa de cadastro nem chave.
API_TRADUCAO = "https://api.mymemory.translated.net/get"

# --- Conversao de Yuan (CN¥) para Real (R$) ---
# Duas fontes gratuitas, sem cadastro. A segunda so e usada se a
# primeira falhar. A cotacao e buscada uma vez por hora, nao a cada
# produto.
FONTES_COTACAO = [
    ("AwesomeAPI", "https://economia.awesomeapi.com.br/last/CNY-BRL"),
    ("ExchangeRate", "https://open.er-api.com/v6/latest/CNY"),
]
VALIDADE_COTACAO = 3600   # segundos (1 hora)

# Mostrar tambem o valor em reais? Desligado: os precos aparecem so em
# Yuan, como o site publica. Para ligar, use MOSTRAR_REAL=sim no .env.
_mostrar_real = False
IDIOMA_DESTINO = "pt-BR"
DELAY_ENTRE_TRADUCOES = 0.5   # segundos entre traducoes (educacao com o servico)
LIMITE_TEXTO_TRADUCAO = 480   # o MyMemory aceita ate ~500 caracteres por vez

# User-Agent honesto: identifica o bot em vez de fingir ser um navegador.
# Isso e boa pratica — o dono do site consegue ver quem esta acessando.
USER_AGENT = "BotColetaPessoal/1.0 (uso pessoal; contato via Telegram)"


# ==========================================================================
#  3. LOG (mostra o progresso na tela e salva no arquivo bot.log)
# ==========================================================================

# Padroes que parecem token/webhook — trocados por "<OCULTO>" antes de
# qualquer linha ir pra tela ou pro arquivo de log. Protege caso voce
# precise colar um trecho do log pra pedir ajuda em algum lugar publico.
_SEGREDOS_NO_LOG = [
    (re.compile(r"\d{6,12}:[A-Za-z0-9_-]{30,}"), "<TOKEN-OCULTO>"),               # token do Telegram
    (re.compile(r"(discord(?:app)?\.com/api/webhooks/\d+/)[A-Za-z0-9_-]+"), r"\1<OCULTO>"),  # webhook do Discord
]


class FormatoSemSegredos(logging.Formatter):
    """Formatter que remove tokens/webhooks das mensagens antes de logar."""
    def format(self, record):
        texto = super().format(record)
        for padrao, troca in _SEGREDOS_NO_LOG:
            texto = padrao.sub(troca, texto)
        return texto


def configurar_log() -> logging.Logger:
    logger = logging.getLogger("bot")
    logger.setLevel(logging.INFO)
    logger.handlers.clear()

    formato = FormatoSemSegredos(
        "%(asctime)s | %(levelname)-7s | %(message)s", datefmt="%d/%m/%Y %H:%M:%S"
    )

    # mostra na tela
    tela = logging.StreamHandler(sys.stdout)
    tela.setFormatter(formato)
    logger.addHandler(tela)

    # salva no arquivo
    arquivo = logging.FileHandler(ARQUIVO_LOG, encoding="utf-8")
    arquivo.setFormatter(formato)
    logger.addHandler(arquivo)

    return logger


log = configurar_log()


# ==========================================================================
#  4. BANCO DE DADOS (SQLite) — guarda os itens e evita duplicatas
# ==========================================================================

def abrir_banco() -> sqlite3.Connection:
    """Abre (ou cria, na primeira vez) o arquivo dados.db."""
    conexao = sqlite3.connect(BANCO_DADOS)
    conexao.execute(
        """
        CREATE TABLE IF NOT EXISTS itens (
            id            TEXT PRIMARY KEY,   -- id do produto no proprio site
            titulo        TEXT NOT NULL,      -- titulo original (chines/ingles)
            titulo_pt     TEXT,               -- titulo traduzido para portugues
            imagem        TEXT,
            link          TEXT,
            preco         TEXT,
            categoria     TEXT,
            plataforma    TEXT,
            origem        TEXT,
            visto_em      TEXT NOT NULL,      -- quando o bot viu pela 1a vez
            notificado    INTEGER DEFAULT 0   -- 0 = ainda nao avisou, 1 = ja avisou
        )
        """
    )
    # Coluna adicionada depois — guarda TODAS as fotos do produto (nao so
    # a primeira), separadas por "|". Banco antigo nao tem essa coluna
    # ainda, entao tentamos criar e ignoramos o erro se ja existir.
    try:
        conexao.execute("ALTER TABLE itens ADD COLUMN imagens TEXT")
    except sqlite3.OperationalError:
        pass
    conexao.commit()
    return conexao


def banco_vazio(conexao: sqlite3.Connection) -> bool:
    """Diz se e a primeirissima vez que o bot roda (banco ainda sem nada)."""
    return conexao.execute("SELECT COUNT(*) FROM itens").fetchone()[0] == 0


def item_ja_existe(conexao: sqlite3.Connection, item_id: str) -> bool:
    cursor = conexao.execute("SELECT 1 FROM itens WHERE id = ?", (item_id,))
    return cursor.fetchone() is not None


def salvar_item(conexao: sqlite3.Connection, item: dict,
                ja_notificado: bool = False) -> None:
    """
    Salva UM item e grava no disco na hora (commit).

    Isso e o 'salvamento incremental': se o script travar no meio, tudo que
    ja foi coletado ate ali continua salvo.

    `ja_notificado=True` e usado so na primeira rodada, para registrar o que
    ja existia no site sem te encher de mensagens.
    """
    conexao.execute(
        """
        INSERT OR IGNORE INTO itens
            (id, titulo, titulo_pt, imagem, imagens, link, preco, categoria,
             plataforma, origem, visto_em, notificado)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            item["id"], item["titulo"], item.get("titulo_pt", ""),
            item["imagem"], "|".join(item.get("imagens") or []), item["link"],
            item["preco"], item["categoria"], item["plataforma"], item["origem"],
            datetime.now().isoformat(timespec="seconds"),
            1 if ja_notificado else 0,
        ),
    )
    conexao.commit()


def buscar_pendentes(conexao: sqlite3.Connection) -> list:
    """
    Devolve os itens que ja estao salvos mas que AINDA NAO foram avisados.

    Por que isso existe: se o .env estiver errado na primeira vez que voce
    rodar, os itens sao salvos mas a mensagem falha. Sem esta funcao, eles
    ficariam presos no banco para sempre e voce nunca seria avisado deles.
    Assim, assim que voce arrumar o .env, o bot manda os atrasados.
    """
    cursor = conexao.execute(
        """
        SELECT id, titulo, titulo_pt, imagem, imagens, link, preco, categoria,
               plataforma, origem
        FROM itens WHERE notificado = 0 ORDER BY visto_em
        """
    )
    return [
        {"id": l[0], "titulo": l[1], "titulo_pt": l[2], "imagem": l[3],
         "imagens": (l[4] or "").split("|") if l[4] else ([l[3]] if l[3] else []),
         "link": l[5], "preco": l[6], "categoria": l[7], "plataforma": l[8],
         "origem": l[9]}
        for l in cursor.fetchall()
    ]


def marcar_notificado(conexao: sqlite3.Connection, item_id: str) -> None:
    conexao.execute("UPDATE itens SET notificado = 1 WHERE id = ?", (item_id,))
    conexao.commit()


# ==========================================================================
#  5. COLETA — baixar a pagina e extrair os dados
# ==========================================================================

def criar_sessao() -> requests.Session:
    """
    Prepara o 'navegador' do bot com retry automatico.

    Se der timeout ou conexao recusada, ele tenta de novo ate 3 vezes,
    esperando um pouco mais a cada tentativa (1s, 2s, 4s).
    """
    sessao = requests.Session()
    sessao.headers.update({"User-Agent": USER_AGENT})

    politica_retry = Retry(
        total=MAX_TENTATIVAS,
        backoff_factor=1,                      # espera 1s, 2s, 4s
        status_forcelist=[429, 500, 502, 503, 504],
        allowed_methods=["GET", "HEAD"],
    )
    adaptador = HTTPAdapter(max_retries=politica_retry)
    sessao.mount("https://", adaptador)
    sessao.mount("http://", adaptador)
    return sessao


# Cache do robots.txt: guarda a ultima resposta por um tempo, em vez de
# buscar o arquivo de novo a cada rodada. Isso tira uma requisicao inteira
# (ida e volta ao site) do caminho critico entre "produto foi lancado" e
# "voce foi avisado" — sem precisar mexer no INTERVALO_SEGUNDOS.
_VALIDADE_CACHE_ROBOTS = 3600   # 1 hora
_cache_robots: dict[str, tuple[bool, float]] = {}


def robots_permite(url: str) -> bool:
    """
    Le o robots.txt do site e confere se o bot tem permissao de acessar.

    IMPORTANTE (corrigido em 16/09/2026): antes, chamavamos leitor.read(),
    que busca o robots.txt por baixo dos panos usando o User-Agent padrao
    do Python ("Python-urllib/x.y"). O Cloudflare do cssdeals passou a
    bloquear esse User-Agent generico (HTTP 403) — e a biblioteca padrao
    do Python, ao receber 401/403, tem uma regra antiga que trata isso
    como "o site proibe TUDO", mesmo que o robots.txt de verdade nao
    proiba nada. Resultado: o bot parava de avisar sem o site ter
    proibido nada de fato.

    A correcao: buscamos o robots.txt NOS MESMOS, com o nosso proprio
    User-Agent (o mesmo usado em todas as outras requisicoes), e so
    entao entregamos o conteudo para o leitor interpretar. Alem disso,
    seguimos a RFC 9309: se o robots.txt vier com erro 4xx (nao existe),
    tratamos como "sem restricoes" em vez de "proibido".

    O resultado fica em cache por _VALIDADE_CACHE_ROBOTS segundos: nao faz
    sentido reler o robots.txt a cada rodada, ja que ele quase nunca muda.
    """
    base = f"{urlparse(url).scheme}://{urlparse(url).netloc}"

    em_cache = _cache_robots.get(base)
    if em_cache and (time.time() - em_cache[1]) < _VALIDADE_CACHE_ROBOTS:
        return em_cache[0]

    leitor = urllib.robotparser.RobotFileParser()
    try:
        resposta = requests.get(
            urljoin(base, "/robots.txt"),
            headers={"User-Agent": USER_AGENT}, timeout=TIMEOUT,
        )
        if resposta.status_code == 200:
            leitor.parse(resposta.text.splitlines())
        elif 400 <= resposta.status_code < 500:
            # Arquivo nao existe / bloqueado por engano -> sem restricoes
            log.warning(
                "robots.txt respondeu HTTP %s. Seguindo sem restricoes.",
                resposta.status_code,
            )
            leitor.parse([])
        else:
            # Erro do lado do site (5xx): nao da pra saber, segue com cautela
            log.warning(
                "robots.txt respondeu HTTP %s. Seguindo com cautela.",
                resposta.status_code,
            )
            leitor.parse([])
    except Exception as erro:
        log.warning("Nao consegui ler o robots.txt (%s). Seguindo com cautela.", erro)
        leitor.parse([])

    permitido = leitor.can_fetch(USER_AGENT, url)
    if not permitido:
        log.error("robots.txt do site PROIBE o acesso a %s — coleta cancelada.", url)
    _cache_robots[base] = (permitido, time.time())
    return permitido


def baixar_pagina(sessao: requests.Session, url: str) -> Optional[str]:
    """Baixa o HTML da pagina. Devolve None se falhar em todas as tentativas."""
    try:
        resposta = sessao.get(url, timeout=TIMEOUT)
        resposta.raise_for_status()
        return resposta.text
    except requests.exceptions.Timeout:
        log.error("Timeout: o site demorou mais de %ss para responder.", TIMEOUT)
    except requests.exceptions.ConnectionError:
        log.error("Conexao recusada ou sem internet.")
    except requests.exceptions.HTTPError as erro:
        log.error("O site respondeu com erro: %s", erro)
    except Exception as erro:
        log.error("Erro inesperado ao baixar a pagina: %s", erro)
    return None


def _buscar_pagina(sessao: requests.Session, categoria: str, numero: int) -> tuple:
    """Busca UMA pagina da API. Devolve (numero, registros) ou (numero, None) se falhar."""
    parametros = {
        "fields": 1,
        "categoryId": categoria,
        "page": numero,
        "pageSize": TAMANHO_PAGINA,
        "priceMin": "0.00",
        "priceMax": "99999.00",
    }

    try:
        resposta = sessao.get(API_PRODUTOS, params=parametros, timeout=TIMEOUT)
        resposta.raise_for_status()
        corpo = resposta.json()
    except requests.exceptions.Timeout:
        log.error("Timeout na pagina %s (%ss).", numero, TIMEOUT)
        return numero, None
    except requests.exceptions.ConnectionError:
        log.error("Conexao recusada ou sem internet (pagina %s).", numero)
        return numero, None
    except requests.exceptions.HTTPError as erro:
        log.error("O site respondeu com erro na pagina %s: %s", numero, erro)
        return numero, None
    except ValueError:
        log.error("O site respondeu algo que nao e JSON na pagina %s.", numero)
        return numero, None
    except Exception as erro:
        log.error("Erro inesperado na pagina %s: %s", numero, erro)
        return numero, None

    if corpo.get("code") != 0:
        log.error("A API recusou a pagina %s: %s", numero, corpo.get("msg") or corpo.get("code"))
        return numero, None

    dados = corpo.get("data") or {}
    if numero == 1 and dados.get("total") is not None:
        log.info("Catalogo do site tem %s produtos no total.", dados["total"])

    return numero, (dados.get("records") or [])


def buscar_lancamentos(sessao: requests.Session, categoria: str = "",
                       paginas: int = 1) -> Optional[list]:
    """
    Pergunta a API do site quais produtos existem, do mais recente para o
    mais antigo.

    `paginas=1` e a leitura mais enxuta possivel. `PAGINAS_RAPIDAS` (2) e
    a leitura de rotina de cada ciclo. `PAGINAS_PROFUNDAS` (10) e a
    varredura funda, que procura produtos que ficaram visiveis agora mas
    foram criados ha dias — esses nascem no meio da lista e o topo nunca
    os mostra.

    Quando pede mais de 1 pagina, busca todas AO MESMO TEMPO (em paralelo,
    ate PAGINAS_SIMULTANEAS por vez) em vez de uma de cada vez — o mesmo
    numero de requisicoes, so que sem ficar esperando fila.
    """
    if paginas <= 1:
        _, registros = _buscar_pagina(sessao, categoria, 1)
        return registros

    from concurrent.futures import ThreadPoolExecutor

    resultados = {}
    with ThreadPoolExecutor(max_workers=PAGINAS_SIMULTANEAS) as executor:
        tarefas = [executor.submit(_buscar_pagina, sessao, categoria, n)
                   for n in range(1, paginas + 1)]
        for tarefa in tarefas:
            numero, registros = tarefa.result()
            resultados[numero] = registros

    # Remonta na ordem certa (1, 2, 3...) e para na primeira pagina que
    # falhou ou veio incompleta (sinal de que chegamos ao fim do catalogo).
    todos = []
    for numero in range(1, paginas + 1):
        registros = resultados.get(numero)
        if registros is None:
            break
        todos.extend(registros)
        if len(registros) < TAMANHO_PAGINA:
            break

    return todos or None


def montar_item(registro: dict) -> Optional[dict]:
    """
    Converte um produto cru da API no formato que o bot usa.

    Pega os tres dados que voce pediu: titulo, primeira foto e link de compra.
    Preco, categoria e plataforma vem junto de graca.
    """
    produto_id = str(registro.get("id") or "").strip()
    if not produto_id:
        return None

    # Titulo: converte codigos de HTML (&#039 vira apostrofo, etc)
    titulo = html.unescape(str(registro.get("title") or "").strip())
    titulo = re.sub(r"\s+", " ", titulo)
    if not titulo:
        titulo = "(produto sem titulo)"

    # Fotos: a lista de produtos (API_PRODUTOS) so traz a capa (campo
    # "thumbnail") — descobrimos que "skus[].image" NAO e uma foto real do
    # produto, e sim uma imagem de referencia interna do fornecedor (outro
    # dominio, geralmente nem bate com o produto certo). As fotos DE
    # VERDADE, as mesmas que aparecem dentro da pagina do produto, só vem
    # de uma segunda chamada (veja enriquecer_com_detalhes mais abaixo),
    # feita so para os itens novos, na hora de avisar.
    skus = registro.get("skus") or []
    primeiro_sku = skus[0] if skus else {}
    imagens = []
    capa = str(registro.get("thumbnail") or "").strip()
    if capa:
        imagens.append(capa)
    imagem = imagens[0] if imagens else ""

    # Preco: a API devolve em yuan; converte para real tambem
    preco = montar_preco(primeiro_sku.get("price"))

    return {
        "id": produto_id,                                   # id do proprio site
        "titulo": titulo,
        "titulo_pt": "",                                    # preenchido depois
        "imagem": imagem,                                   # foto principal (compatibilidade)
        "imagens": imagens,                                 # todas as fotos, na ordem
        "link": URL_PRODUTO.format(id=produto_id),          # pagina do produto
        "link_compra": URL_COMPRA.format(id=produto_id) + CSSBUY_EXTRA,  # botao "comprar agora"
        "preco": preco,
        "categoria": CATEGORIAS.get(str(registro.get("categoryId") or ""), ""),
        "plataforma": PLATAFORMAS.get(registro.get("salePlatform"), ""),
        "origem": str(registro.get("sourceLink") or "").strip(),
        "cor": "Padrão",                                     # preenchido depois, se houver
        "tamanho": "Padrão",                                 # preenchido depois, se houver
    }


def extrair_itens(registros: list) -> list:
    """Converte a lista crua da API em itens, descartando os invalidos."""
    itens = []
    for registro in registros:
        item = montar_item(registro)
        if item:
            itens.append(item)
    return itens


def buscar_detalhe_produto(sessao: requests.Session, produto_id: str) -> Optional[dict]:
    """
    Busca os detalhes de UM produto especifico — as fotos reais da pagina
    dele, a variacao (cor/tamanho) e o link de origem.

    Usa um timeout CURTO (TIMEOUT_DETALHE) de proposito: isto roda na hora
    de avisar, entao se o site demorar, desistimos rapido e mandamos o
    aviso do mesmo jeito, so que com a capa em vez das fotos reais — nunca
    vale a pena atrasar o aviso esperando essa chamada extra.
    """
    try:
        resposta = sessao.get(
            API_PRODUTO_DETALHE.format(id=produto_id), timeout=TIMEOUT_DETALHE,
        )
        resposta.raise_for_status()
        corpo = resposta.json()
    except Exception as erro:
        log.warning("Nao consegui buscar os detalhes de %s (%s). Usando a capa.", produto_id, erro)
        return None

    if corpo.get("code") != 0:
        return None

    return corpo.get("data") or None


def _limpar_texto_variacao(valor: str) -> str:
    """Remove anotacoes entre parenteses e pontuacao sobrando de um pedaco de variacao."""
    valor = re.sub(r"[\(（][^)）]*[\)）]", "", valor)          # tira "(No Print)", "（No Badge）"
    valor = valor.replace("：", ":").replace("；", ";")        # pontuacao de largura total -> normal
    return valor.strip(" :;,\u3000")


def _limpar_cor(valor: str) -> str:
    """Alem de limpar, tira codigos internos (ex: '2425AC') que vem colados na cor."""
    valor = _limpar_texto_variacao(valor)
    palavras = valor.split()
    # Codigo interno: mistura letra+numero, sem espaco, curto (ex: 2425AC, CD001)
    while palavras and re.match(r"^(?=.*[0-9])(?=.*[A-Za-z])[A-Za-z0-9]{2,8}$", palavras[0]):
        palavras.pop(0)
    valor = " ".join(palavras).strip()
    return valor[:1].upper() + valor[1:] if valor else ""


def interpretar_variacao(skuNames: str) -> tuple:
    """
    Extrai cor e tamanho de um texto de variacao cru, tipo:
    'Color Classification:away：（No Print）;Size:2XL ( No Badge );'
    ou 'Cor:2425AC fora de casa;Tamanho:XXL;'

    Alguns produtos (tenis, por exemplo) nao rotulam o valor — vem so
    '44', sem nenhum 'Size:' ou 'Tamanho:' na frente. Nesse caso, se o
    valor sobrando parecer um numero/tamanho, ele CONTA como tamanho —
    "Padrao" e reservado so pra quando nao ha NENHUMA informacao no sku.

    Devolve (cor, tamanho), cada um "Padrao" se nao achar nada mesmo.
    """
    cor, tamanho = "", ""
    achou_rotulo = False

    if skuNames:
        for rotulo, valor in re.findall(
            r"(cor|color(?:\s*classification)?|tamanho|size)\s*[:：]\s*([^;&]+)",
            skuNames, re.IGNORECASE,
        ):
            achou_rotulo = True
            if rotulo.lower().startswith(("cor", "color")):
                cor = _limpar_cor(valor) or cor
            else:
                tamanho = _limpar_texto_variacao(valor) or tamanho

        # Nenhum rotulo "Cor:"/"Tamanho:" encontrado — o site so mandou um
        # valor solto (ex: so "44"). Se parecer numero/tamanho, usa como
        # tamanho; senao, assume que e uma cor/variacao sem nome de campo.
        if not achou_rotulo:
            texto = skuNames
            if "&" in texto or texto.startswith("sku="):
                # formato de query string: pega SO a parte do "sku=",
                # ignorando "sku_id=" (que e outra coisa, nao a variacao)
                partes = [p[4:] for p in texto.split("&") if p.startswith("sku=")]
                texto = partes[0] if partes else ""
            sobra = _limpar_texto_variacao(texto)
            if sobra:
                if re.match(r"^\d{1,3}(\.\d+)?$|^(XX?S|S|M|L|XX?L|XXX?L)$", sobra, re.IGNORECASE):
                    tamanho = sobra
                else:
                    cor = _limpar_cor(sobra)

    return cor or "Padrão", tamanho or "Padrão"


def _aplicar_detalhe_no_item(item: dict, detalhe: dict) -> None:
    """Aplica as fotos reais, variacao (cor/tamanho) e link de origem de um `detalhe` no item."""
    fotos_reais = [
        str(foto.get("url") or "").strip() + REDIMENSIONA_FOTO
        for foto in (detalhe.get("images") or [])
        if str(foto.get("url") or "").strip()
    ]
    if fotos_reais:
        item["imagens"] = fotos_reais
        item["imagem"] = fotos_reais[0]

    skus = detalhe.get("skus") or []
    if skus:
        item["cor"], item["tamanho"] = interpretar_variacao(str(skus[0].get("skuNames") or ""))
        origem = str(skus[0].get("sourceLink") or "").strip()
        if origem:
            item["origem"] = origem


def enriquecer_com_detalhes(sessao: requests.Session, item: dict) -> None:
    """
    Completa o item com as fotos reais, a variacao (cor/tamanho) e o link
    de origem, buscando na pagina do proprio produto.

    Se essa busca falhar por qualquer motivo, o item fica como estava (com
    a capa) — nunca impede o aviso de ser enviado.
    """
    detalhe = buscar_detalhe_produto(sessao, item["id"])
    if detalhe:
        _aplicar_detalhe_no_item(item, detalhe)


def montar_item_do_detalhe(detalhe: dict) -> Optional[dict]:
    """
    Monta um item completo a partir de uma resposta do endpoint de
    DETALHE (e nao da listagem). Usado para reavisar um produto que
    esgotou e voltou ao estoque — nesse ponto so temos o id, entao
    buscamos tudo de novo direto na pagina do produto.
    """
    item = montar_item(detalhe)
    if item:
        _aplicar_detalhe_no_item(item, detalhe)
    return item


def quantidade_total(detalhe: dict) -> int:
    """Soma o estoque de todas as variacoes (skus) de um produto."""
    total = 0
    for sku in (detalhe.get("skus") or []):
        try:
            total += int(sku.get("quantity") or 0)
        except (TypeError, ValueError):
            pass
    return total


def carregar_estoque(caminho: str) -> dict:
    """Le o arquivo de vigilancia de estoque. Se nao existir, devolve vazio."""
    if not os.path.exists(caminho):
        return {}
    try:
        with open(caminho, "r", encoding="utf-8") as arquivo:
            return json.load(arquivo)
    except (OSError, ValueError) as erro:
        log.warning("Nao consegui ler %s (%s). Comecando do zero.", caminho, erro)
        return {}


def salvar_estoque(caminho: str, mapa: dict) -> None:
    """Grava o arquivo de vigilancia, mantendo so os REESTOQUE_MAX_ITENS mais recentes."""
    recentes = dict(list(mapa.items())[-REESTOQUE_MAX_ITENS:])
    temporario = caminho + ".tmp"
    try:
        with open(temporario, "w", encoding="utf-8") as arquivo:
            json.dump(recentes, arquivo)
        os.replace(temporario, caminho)
    except OSError as erro:
        log.warning("Nao consegui salvar %s (%s).", caminho, erro)


def verificar_reestoques(sessao: requests.Session, mapa_estoque: dict) -> list:
    """
    Reconfere o estoque de todos os produtos sob vigilancia (mapa_estoque)
    em paralelo. Devolve a lista de itens que ESGOTARAM E VOLTARAM — os
    unicos que precisam de um novo aviso. Atualiza mapa_estoque no lugar.

    Uma falha ao checar um produto especifico (site fora do ar, produto
    removido) so deixa o status como estava — nunca derruba a rodada.
    """
    if not mapa_estoque:
        return []

    from concurrent.futures import ThreadPoolExecutor

    ids = list(mapa_estoque.keys())
    reestocados = []

    with ThreadPoolExecutor(max_workers=REESTOQUE_SIMULTANEAS) as executor:
        tarefas = {executor.submit(buscar_detalhe_produto, sessao, id_): id_ for id_ in ids}
        for tarefa in tarefas:
            id_ = tarefas[tarefa]
            try:
                detalhe = tarefa.result()
            except Exception as erro:
                log.warning("Falha ao reconferir estoque de %s (%s).", id_, erro)
                continue
            if not detalhe:
                continue   # produto pode ter saido do ar — mantem status antigo

            disponivel_agora = quantidade_total(detalhe) > 0
            status_anterior = mapa_estoque.get(id_)

            if status_anterior == "esgotado" and disponivel_agora:
                item = montar_item_do_detalhe(detalhe)
                if item:
                    item["reestoque"] = True
                    reestocados.append(item)
                mapa_estoque[id_] = "disponivel"
            elif status_anterior != "esgotado" and not disponivel_agora:
                mapa_estoque[id_] = "esgotado"
            else:
                mapa_estoque[id_] = "disponivel" if disponivel_agora else "esgotado"

    return reestocados


def _caminho_estoque(caminho_base: str) -> str:
    """Deriva o nome do arquivo de vigilancia de estoque a partir de outro caminho."""
    base, _ext = os.path.splitext(caminho_base)
    return base + ".estoque.json"


def buscar_por_titulo(termo: str, quantos: int = 10) -> list:
    """Procura no catalogo produtos cujo titulo contenha o termo (a propria API filtra)."""
    parametros = {
        "fields": 1, "categoryId": "", "page": 1, "pageSize": quantos,
        "priceMin": "0.00", "priceMax": "99999.00", "title": termo,
    }
    try:
        resposta = requests.get(
            API_PRODUTOS, params=parametros,
            headers={"User-Agent": USER_AGENT}, timeout=TIMEOUT,
        )
        resposta.raise_for_status()
        corpo = resposta.json()
    except Exception as erro:
        log.error("Busca falhou: %s", erro)
        return []
    if corpo.get("code") != 0:
        log.error("A API recusou a busca: %s", corpo.get("msg"))
        return []
    return (corpo.get("data") or {}).get("records") or []


def comando_buscar(termo: str) -> None:
    """Comando de terminal (--buscar "termo"): mostra os produtos achados com TODAS as fotos."""
    print()
    print("=" * 66)
    print("  BUSCA: {}".format(termo))
    print("=" * 66)

    achados = buscar_por_titulo(termo)
    if not achados:
        print()
        print("  Nenhum produto encontrado com esse texto no titulo.")
        print("  Tente um trecho menor, ou uma palavra so.")
        print()
        return

    sessao = criar_sessao()
    for numero, registro in enumerate(achados, 1):
        item = montar_item(registro) or {}
        detalhe = buscar_detalhe_produto(sessao, registro.get("id", "")) or {}
        fotos = [f.get("url") for f in (detalhe.get("images") or []) if f.get("url")]
        sku = (detalhe.get("skus") or registro.get("skus") or [{}])[0]

        print()
        print("  {}. {}".format(numero, (registro.get("title") or "")[:60]))
        print("     {}   tamanho {}   estoque {}".format(
            montar_preco(sku.get("price")) or "?", sku.get("size") or "-",
            sku.get("quantity", "?"),
        ))
        print("     {}".format(item.get("link", "")))
        if fotos:
            print("     FOTOS ({}):".format(len(fotos)))
            for foto in fotos:
                print("       {}".format(foto))
        else:
            print("     (sem fotos no detalhe)")

    print()
    print("=" * 66)
    print("  As imagens continuam acessiveis mesmo se o anuncio sair do ar.")
    print("  Salve os enderecos acima se quiser guardar.")
    print("=" * 66)


def testar_rede() -> None:
    """
    Comando de terminal (--testar-rede): confere se ESTE servidor alcanca
    cada servico usado pelo bot, por IPv4 e por IPv6 separadamente.

    Existe porque a mensagem de erro do Python engana: quando o IPv4
    demora e o IPv6 nao tem rota (ou vice-versa), so aparece o ULTIMO
    erro tentado, escondendo qual dos dois realmente falhou.
    """
    import socket

    def alcanca(host: str, familia) -> str:
        try:
            enderecos = socket.getaddrinfo(host, 443, familia, socket.SOCK_STREAM)
        except socket.gaierror:
            return "sem endereco nesse protocolo"
        for af, tipo, proto, _, destino in enderecos[:2]:
            sock = socket.socket(af, tipo, proto)
            sock.settimeout(5)
            try:
                sock.connect(destino)
                return "OK"
            except OSError as erro:
                return "falhou ({})".format(erro)
            finally:
                sock.close()
        return "sem endereco nesse protocolo"

    print()
    print("=" * 66)
    print("  DIAGNOSTICO DE REDE")
    print("=" * 66)

    hosts = [
        ("cssdeals.com", urlparse(SITE_BASE).netloc),
        ("api.telegram.org", "api.telegram.org"),
        ("discord.com", "discord.com"),
    ]
    for nome, host in hosts:
        print()
        print("  {}:".format(nome))
        print("     IPv4: {}".format(alcanca(host, socket.AF_INET)))
        print("     IPv6: {}".format(alcanca(host, socket.AF_INET6)))

    print()
    print("=" * 66)
    print("  Se um servico falha so no IPv6, o problema costuma ser o")
    print("  provedor de hospedagem (falta de rota), nao o seu codigo.")
    print("=" * 66)


# ==========================================================================
#  4.5 MEMORIA EM ARQUIVO DE TEXTO  (para rodar hospedado fora do Mac)
# ==========================================================================
#  Quando o bot roda no GitHub Actions, o computador e apagado ao fim de
#  cada rodada. O banco SQLite nao sobrevive — e, por ser um arquivo
#  binario, versiona-lo a cada 15 minutos incharia o repositorio.
#
#  Entao neste modo a memoria vira um arquivo de texto simples: uma linha
#  por produto ja avisado. Ocupa quase nada, o Git versiona bem e voce
#  consegue abrir e ler se quiser.
# ==========================================================================

# Quantos ids guardar. Precisa ser bem maior que a janela profunda
# (1000 produtos), senao ids esquecidos voltariam a parecer novos.
MAX_IDS_ESTADO = 4000


def carregar_estado(caminho: str) -> list:
    """Le o arquivo de memoria. Se nao existir ainda, devolve lista vazia."""
    if not os.path.exists(caminho):
        return []
    try:
        with open(caminho, "r", encoding="utf-8") as arquivo:
            return [l.strip() for l in arquivo if l.strip() and not l.startswith("#")]
    except OSError as erro:
        log.warning("Nao consegui ler %s (%s). Comecando do zero.", caminho, erro)
        return []


def salvar_estado(caminho: str, ids: list) -> None:
    """
    Grava a memoria, mantendo so os mais recentes.

    Escreve primeiro num arquivo temporario e so depois substitui o
    definitivo — assim, se faltar energia no meio, o arquivo antigo
    continua intacto em vez de virar lixo.
    """
    recentes = ids[-MAX_IDS_ESTADO:]
    temporario = caminho + ".tmp"
    try:
        with open(temporario, "w", encoding="utf-8") as arquivo:
            arquivo.write("# Produtos que o bot ja avisou. Nao edite a mao.\n")
            arquivo.write("\n".join(recentes) + "\n")
        os.replace(temporario, caminho)
    except OSError as erro:
        log.error("Nao consegui gravar a memoria em %s: %s", caminho, erro)


# ==========================================================================
#  5.4 COTACAO: CONVERTER YUAN PARA REAL
# ==========================================================================
#  Os precos do site vem em Yuan chines. Aqui viram reais, para voce nao
#  precisar fazer a conta de cabeca a cada anuncio.
# ==========================================================================

# Guarda a ultima cotacao e a hora em que foi buscada
_cotacao = {"valor": None, "quando": 0.0}


def cotacao_cny_brl() -> Optional[float]:
    """
    Quanto vale 1 Yuan em reais.

    Busca uma vez por hora e reaproveita. Se as duas fontes falharem,
    devolve None — e o bot mostra so o preco em Yuan, sem quebrar.
    """
    agora = time.time()
    if _cotacao["valor"] and (agora - _cotacao["quando"]) < VALIDADE_COTACAO:
        return _cotacao["valor"]

    for nome, url in FONTES_COTACAO:
        try:
            resposta = requests.get(
                url, headers={"User-Agent": USER_AGENT}, timeout=TIMEOUT
            )
            resposta.raise_for_status()
            corpo = resposta.json()

            if "awesomeapi" in url:
                valor = float(corpo["CNYBRL"]["bid"])
            else:
                valor = float(corpo["rates"]["BRL"])

            # Sanidade: se vier um numero absurdo, e sinal de que a
            # fonte mudou o formato — melhor ignorar do que mostrar
            # um preco errado para voce.
            if not (0.1 < valor < 10):
                log.warning("Cotacao suspeita da %s: %s. Ignorando.", nome, valor)
                continue

            _cotacao["valor"] = valor
            _cotacao["quando"] = agora
            log.info("Cotacao (%s): 1 CN¥ = R$ %.4f", nome, valor)
            return valor

        except Exception as erro:
            log.warning("Fonte de cotacao %s falhou: %s", nome, str(erro)[:80])

    log.warning("Nenhuma fonte de cotacao respondeu. Mostrando so em Yuan.")
    return None


def formatar_numero(valor: float) -> str:
    """Formata no padrao brasileiro: 1.234,56 em vez de 1,234.56."""
    texto = "{:,.2f}".format(valor)
    return texto.replace(",", "\x00").replace(".", ",").replace("\x00", ".")


def montar_preco(valor_yuan) -> str:
    """
    Monta o texto do preco: Yuan e, quando possivel, o valor em reais.

    Exemplo:  CN¥ 30,19  (~R$ 23,12)
    """
    if valor_yuan is None:
        return ""

    try:
        yuan = float(valor_yuan)
    except (TypeError, ValueError):
        return ""

    texto = "CN¥ {}".format(formatar_numero(yuan))

    # So consulta a cotacao se voce tiver pedido a conversao
    if _mostrar_real:
        taxa = cotacao_cny_brl()
        if taxa:
            texto += "  (~R$ {})".format(formatar_numero(yuan * taxa))

    return texto


# ==========================================================================
#  5.5 TRADUCAO DOS TITULOS
# ==========================================================================
#  Os produtos vem do Taobao/Weidian/1688, entao os titulos chegam em
#  chines ou em ingles. Aqui eles viram portugues.
#
#  Cada traducao e guardada no banco. Se o mesmo titulo aparecer de novo,
#  o bot usa a traducao salva em vez de pedir outra vez — isso economiza
#  a cota do servico gratuito e deixa tudo mais rapido.
# ==========================================================================

# Fica True se a cota diaria acabar, para nao insistir a rodada inteira
_traducao_indisponivel = False


def criar_cache_traducao(conexao: sqlite3.Connection) -> None:
    """Cria a tabelinha que guarda as traducoes ja feitas."""
    conexao.execute(
        """
        CREATE TABLE IF NOT EXISTS traducoes (
            original   TEXT PRIMARY KEY,
            traduzido  TEXT NOT NULL
        )
        """
    )
    conexao.commit()


# Cache em memoria, usado quando nao ha banco (modo GitHub Actions)
_cache_memoria = {}


def traducao_no_cache(conexao, texto: str) -> Optional[str]:
    if conexao is None:
        return _cache_memoria.get(texto)
    linha = conexao.execute(
        "SELECT traduzido FROM traducoes WHERE original = ?", (texto,)
    ).fetchone()
    return linha[0] if linha else None


def guardar_traducao(conexao, texto: str, traduzido: str) -> None:
    if conexao is None:
        _cache_memoria[texto] = traduzido
        return
    conexao.execute(
        "INSERT OR REPLACE INTO traducoes (original, traduzido) VALUES (?, ?)",
        (texto, traduzido),
    )
    conexao.commit()


def detectar_idioma(texto: str) -> str:
    """
    Descobre se o titulo esta em chines ou em ingles.

    Simples e eficaz: se tiver ideograma chines no meio, e chines.
    """
    for caractere in texto:
        if "\u4e00" <= caractere <= "\u9fff":   # faixa dos ideogramas chineses
            return "zh-CN"
    return "en"


def traduzir(texto: str, conexao, email: str = "") -> str:
    """
    Traduz um titulo para portugues.

    Se qualquer coisa der errado (sem internet, cota esgotada, servico fora
    do ar), devolve o titulo ORIGINAL em vez de quebrar. Voce nunca deixa de
    receber a notificacao por causa da traducao.
    """
    global _traducao_indisponivel

    texto = (texto or "").strip()
    if not texto:
        return texto

    # 1) Ja traduzimos esse titulo antes?
    salva = traducao_no_cache(conexao, texto)
    if salva is not None:
        return salva

    # 2) A cota acabou nesta rodada? Nao adianta tentar de novo.
    if _traducao_indisponivel:
        return texto

    recorte = texto[:LIMITE_TEXTO_TRADUCAO]
    parametros = {
        "q": recorte,
        "langpair": "{}|{}".format(detectar_idioma(texto), IDIOMA_DESTINO),
    }
    if email:
        parametros["de"] = email      # informar um e-mail aumenta a cota diaria

    try:
        resposta = requests.get(
            API_TRADUCAO, params=parametros,
            headers={"User-Agent": USER_AGENT}, timeout=TIMEOUT,
        )
        resposta.raise_for_status()
        corpo = resposta.json()
    except Exception as erro:
        log.warning("Traducao falhou (%s). Mantendo o titulo original.", erro)
        return texto

    # Cota diaria estourada
    if corpo.get("quotaFinished"):
        _traducao_indisponivel = True
        log.warning(
            "A cota diaria de traducao acabou. Os titulos continuam chegando, "
            "so que no idioma original. Volta ao normal amanha. "
            "(Dica: preencher TRADUCAO_EMAIL no .env aumenta bastante a cota.)"
        )
        return texto

    if corpo.get("responseStatus") != 200:
        log.warning(
            "Servico de traducao recusou: %s. Mantendo o titulo original.",
            str(corpo.get("responseDetails"))[:100],
        )
        return texto

    traduzido = str((corpo.get("responseData") or {}).get("translatedText") or "").strip()
    if not traduzido:
        return texto

    # O MyMemory as vezes devolve um aviso em vez da traducao
    if "QUERY LENGTH LIMIT" in traduzido.upper() or "INVALID" in traduzido.upper():
        return texto

    guardar_traducao(conexao, texto, traduzido)
    time.sleep(DELAY_ENTRE_TRADUCOES)
    return traduzido


# ==========================================================================
#  6. NOTIFICACOES — Telegram e Discord
# ==========================================================================

def titulo_visivel(item: dict) -> str:
    """Titulo em portugues quando existe; senao, o original."""
    return (item.get("titulo_pt") or "").strip() or item["titulo"]


def montar_texto_telegram(item: dict) -> str:
    """Monta a mensagem no formato HTML do Telegram (negrito, link clicavel)."""
    etiqueta = "🔄 VOLTOU AO ESTOQUE" if item.get("reestoque") else "\U0001F195 NOVO"
    linhas = ["{} <b>{}</b>".format(etiqueta, escapar_html(titulo_visivel(item)))]

    # Mostra o titulo original tambem — util para procurar o produto no site
    original = item["titulo"]
    if original and original != titulo_visivel(item):
        linhas.append("<i>{}</i>".format(escapar_html(original)))

    etiquetas = [e for e in (item.get("categoria"), item.get("plataforma")) if e]
    if etiquetas:
        linhas.append(escapar_html(" · ".join(etiquetas)))

    # "COMPRAR AGORA" em destaque, logo no topo
    if item.get("link_compra"):
        linhas.append('🛒 <b><a href="{}">COMPRAR AGORA</a></b>'.format(item["link_compra"]))

    linhas.append("")
    linhas.append("💰 Preço: <b>{}</b>".format(escapar_html(item.get("preco") or "N/A")))
    linhas.append("📏 Tamanho: <b>{}</b>".format(escapar_html(item.get("tamanho") or "Padrão")))
    linhas.append("🎨 Cor: <b>{}</b>".format(escapar_html(item.get("cor") or "Padrão")))

    if item.get("link"):
        linhas.append('📄 <a href="{}">Ver no CSSDeals</a>'.format(item["link"]))

    # Link de origem e ID: mais abaixo e sem destaque (italico) — o link
    # mostra so o texto "Acessar Fonte", clicavel, nunca a URL inteira.
    rodape = []
    if item.get("origem"):
        rodape.append('🔗 <a href="{}">Acessar Fonte</a>'.format(item["origem"]))
    rodape.append("🆔 {}".format(escapar_html(item["id"])))
    linhas.append("<i>{}</i>".format(" · ".join(rodape)))

    if item.get("publicado_em"):
        horario = item["publicado_em"].strftime("%d/%m/%Y %H:%M UTC")
        linhas.append(escapar_html("Publicado: {}".format(horario)))

    return "\n".join(linhas)


def escapar_html(texto: str) -> str:
    """Protege caracteres especiais para nao quebrar a formatacao do Telegram."""
    return texto.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def enviar_telegram(item: dict, token: str, chat_id: str) -> bool:
    """
    Envia UM item para o grupo do Telegram.

    Se o item tem 2+ fotos, manda um album (todas as fotos juntas, legenda
    so na primeira). Se tem 1 foto, manda ela com legenda. Se nao tem foto
    (ou o envio falhar), manda so o texto. Devolve True se conseguiu enviar.
    """
    texto = montar_texto_telegram(item)
    base = f"https://api.telegram.org/bot{token}"
    imagens = item.get("imagens") or ([item["imagem"]] if item.get("imagem") else [])

    # Tentativa 1: album com todas as fotos (Telegram aceita ate 10)
    if len(imagens) > 1:
        midia = [
            {"type": "photo", "media": url}
            for url in imagens[:10]
        ]
        midia[0]["caption"] = texto
        midia[0]["parse_mode"] = "HTML"
        ok = _post_telegram(
            f"{base}/sendMediaGroup",
            {"chat_id": chat_id, "media": midia},
            como_json=True,
        )
        if ok:
            return True
        log.warning("Nao deu para mandar o album de fotos. Tentando so a primeira...")

    # Tentativa 2: mandar so a primeira foto
    if imagens:
        ok = _post_telegram(
            f"{base}/sendPhoto",
            {
                "chat_id": chat_id,
                "photo": imagens[0],
                "caption": texto,
                "parse_mode": "HTML",
            },
        )
        if ok:
            return True
        log.warning("Nao deu para mandar a foto. Tentando so com texto...")

    # Tentativa 3 (ou unica): so texto
    return _post_telegram(
        f"{base}/sendMessage",
        {
            "chat_id": chat_id,
            "text": texto,
            "parse_mode": "HTML",
            "disable_web_page_preview": False,
        },
    )


def _post_telegram(url: str, dados: dict, como_json: bool = False) -> bool:
    """
    Faz o envio de fato e trata os erros SEM derrubar o script.

    `como_json=True` e usado pelo sendMediaGroup, que precisa do campo
    "media" como lista de verdade (envio normal em forms nao suporta isso).

    Erros tratados:
      - 429 (rate limit): espera o tempo que o Telegram pedir e tenta de novo
      - 403 (bot sem permissao no grupo): avisa no log e segue
      - qualquer outro: loga e segue
    """
    for tentativa in range(1, MAX_TENTATIVAS + 1):
        try:
            if como_json:
                resposta = requests.post(url, json=dados, timeout=TIMEOUT)
            else:
                resposta = requests.post(url, data=dados, timeout=TIMEOUT)

            if resposta.status_code == 200:
                return True

            corpo = resposta.json() if resposta.content else {}
            descricao = corpo.get("description", resposta.text[:200])

            # Rate limit: o Telegram diz quantos segundos esperar
            if resposta.status_code == 429:
                espera = corpo.get("parameters", {}).get("retry_after", 5)
                log.warning("Limite do Telegram atingido. Esperando %ss...", espera)
                time.sleep(espera + 1)
                continue

            # Bot sem permissao / expulso do grupo — nao adianta insistir
            if resposta.status_code in (401, 403):
                log.error(
                    "TELEGRAM SEM PERMISSAO (%s): %s "
                    "-> Confira se o bot foi adicionado ao grupo e se o "
                    "TELEGRAM_CHAT_ID esta correto.",
                    resposta.status_code, descricao,
                )
                return False

            if resposta.status_code == 400:
                # Caso especial: o grupo virou supergrupo e trocou de ID.
                # O Telegram informa o ID novo na propria resposta — vamos
                # mostra-lo, em vez de deixar voce procurando.
                novo_id = corpo.get("parameters", {}).get("migrate_to_chat_id")
                if novo_id:
                    log.error("=" * 60)
                    log.error("O GRUPO VIROU SUPERGRUPO E MUDOU DE ID.")
                    log.error("")
                    log.error("   ID antigo (o que esta configurado): %s", dados.get("chat_id"))
                    log.error("   ID NOVO (use este):                 %s", novo_id)
                    log.error("")
                    log.error("   Troque TELEGRAM_CHAT_ID para %s", novo_id)
                    log.error("   nas Variables do Railway. E so isso.")
                    log.error("=" * 60)
                else:
                    log.error("TELEGRAM recusou a mensagem (400): %s", descricao)
                return False

            log.warning(
                "Telegram devolveu erro %s (tentativa %s/%s): %s",
                resposta.status_code, tentativa, MAX_TENTATIVAS, descricao,
            )
            time.sleep(2 * tentativa)

        except requests.exceptions.RequestException as erro:
            log.warning(
                "Falha de rede ao falar com o Telegram (tentativa %s/%s): %s",
                tentativa, MAX_TENTATIVAS, erro,
            )
            time.sleep(2 * tentativa)

    log.error("Desisti de enviar esta mensagem no Telegram apos %s tentativas.", MAX_TENTATIVAS)
    return False


def enviar_discord(item: dict, webhook_url: str) -> bool:
    """
    Envia UM item para o canal do Discord usando um Webhook.

    O Discord monta um card bonito (embed) com titulo, link e foto.
    """
    prefixo = "🔄 VOLTOU AO ESTOQUE: " if item.get("reestoque") else ""
    embed = {
        "title": (prefixo + titulo_visivel(item))[:250],
        "color": 0xFFA500 if item.get("reestoque") else 0x00B37E,   # laranja pro reestoque, verde pro lancamento
    }
    if item.get("link"):
        embed["url"] = item["link"]
    imagens = item.get("imagens") or ([item["imagem"]] if item.get("imagem") else [])
    if imagens:
        embed["image"] = {"url": imagens[0]}
    # Horario em que o bot detectou/publicou o lancamento. O Discord mostra
    # isso automaticamente no rodape do card, JA CONVERTIDO para o fuso
    # horario de cada pessoa que ve a mensagem (nao precisa formatar nada).
    if item.get("publicado_em"):
        embed["timestamp"] = item["publicado_em"].isoformat()

    # "COMPRAR AGORA" em destaque no topo do card. Igual ao Link Original,
    # evitamos o formato "[texto](link)" aqui tambem — em vez de um texto
    # bonito clicavel, mostramos o rotulo em negrito e a URL crua logo
    # abaixo. Fica menos elegante, mas o negrito e o link SEMPRE
    # funcionam, sem depender do bug de link mascarado do Discord.
    linhas_descricao = []
    if item.get("link_compra"):
        linhas_descricao.append("🛒 **COMPRAR AGORA**\n{}".format(item["link_compra"]))
    original = item["titulo"]
    if original and original != titulo_visivel(item):
        linhas_descricao.append("*{}*".format(original[:200]))
    etiquetas = [e for e in (item.get("categoria"), item.get("plataforma")) if e]
    if etiquetas:
        linhas_descricao.append(" · ".join(etiquetas))
    if linhas_descricao:
        embed["description"] = "\n".join(linhas_descricao)

    # Preco / Tamanho / Cor lado a lado, em destaque (campos "inline"
    # ficam em coluna, o Discord encaixa 3 por linha sozinho).
    embed["fields"] = [
        {"name": "💰 Preço", "value": item.get("preco") or "N/A", "inline": True},
        {"name": "📏 Tamanho", "value": item.get("tamanho") or "Padrão", "inline": True},
        {"name": "🎨 Cor", "value": item.get("cor") or "Padrão", "inline": True},
    ]
    # Link de origem e ID: mais abaixo e sem destaque (lado a lado,
    # ocupando menos espaco que os campos de cima).
    #
    # IMPORTANTE: o formato "[texto](link)" (link mascarado) tem um bug
    # CONHECIDO do proprio Discord — falha e mostra tudo cru de vez em
    # quando, sem padrao claro de quando acontece (bug aberto no
    # rastreador oficial deles). Por isso, paramos de usar esse formato
    # aqui: colamos a URL crua mesmo, que o Discord SEMPRE transforma em
    # link clicavel sozinho, sem depender de nenhum markdown.
    if item.get("origem"):
        embed["fields"].append({
            "name": "🔗 Link Original",
            "value": item["origem"],
            "inline": False,
        })
    embed["fields"].append({"name": "🆔 ID", "value": item["id"], "inline": True})

    # Fotos extras: o Discord agrupa varios embeds numa unica galeria
    # quando todos compartilham a mesma "url" — por isso os embeds extras
    # so tem a foto, sem repetir titulo/descricao.
    embeds = [embed]
    if item.get("link"):
        for extra in imagens[1:MAX_IMAGENS_DISCORD]:
            embeds.append({"url": item["link"], "image": {"url": extra}})

    # Botao (alem do link em destaque na descricao): reforco visual, mas
    # nao e a unica forma de comprar — se o Webhook recusar botao, o link
    # da descricao acima continua funcionando.
    componentes = []
    if item.get("link_compra"):
        componentes = [{"type": 1, "components": [
            {"type": 2, "style": 5, "label": "🛒 COMPRAR AGORA", "url": item["link_compra"]},
        ]}]

    for tentativa in range(1, MAX_TENTATIVAS + 1):
        try:
            payload = {"embeds": embeds}
            if componentes:
                payload["components"] = componentes
            # LOG TEMPORARIO DE DIAGNOSTICO: mostra exatamente o que estamos
            # mandando pro Discord, pra confirmar se o "COMPRAR AGORA" esta
            # saindo daqui ou se some depois (do lado do Discord).
            log.info("DIAGNOSTICO description enviada: %r", embed.get("description"))
            resposta = requests.post(webhook_url, json=payload, timeout=TIMEOUT)
            if resposta.status_code not in (200, 204):
                log.warning(
                    "Discord respondeu %s: %s", resposta.status_code, resposta.text[:500]
                )

            # Se o Discord recusar por causa dos botoes (webhook antigo,
            # sem suporte a componentes), tenta de novo so com os embeds —
            # melhor mandar sem botao do que nao mandar nada.
            if resposta.status_code == 400 and componentes:
                log.warning("Discord recusou os botoes — mandando sem eles.")
                componentes = []
                resposta = requests.post(
                    webhook_url, json={"embeds": embeds}, timeout=TIMEOUT
                )

            if resposta.status_code in (200, 204):
                return True

            # Rate limit do Discord
            if resposta.status_code == 429:
                corpo = resposta.json() if resposta.content else {}
                espera = float(corpo.get("retry_after", 5))
                log.warning("Limite do Discord atingido. Esperando %.1fs...", espera)
                time.sleep(espera + 1)
                continue

            if resposta.status_code in (401, 403, 404):
                log.error(
                    "DISCORD recusou (%s) -> a URL do webhook parece invalida "
                    "ou foi apagada. Gere um webhook novo no canal.",
                    resposta.status_code,
                )
                return False

            log.warning(
                "Discord devolveu erro %s (tentativa %s/%s): %s",
                resposta.status_code, tentativa, MAX_TENTATIVAS, resposta.text[:200],
            )
            time.sleep(2 * tentativa)

        except requests.exceptions.RequestException as erro:
            log.warning(
                "Falha de rede ao falar com o Discord (tentativa %s/%s): %s",
                tentativa, MAX_TENTATIVAS, erro,
            )
            time.sleep(2 * tentativa)

    log.error("Desisti de enviar esta mensagem no Discord apos %s tentativas.", MAX_TENTATIVAS)
    return False


def notificar(item: dict, config: dict) -> bool:
    """
    Manda o item para todos os canais configurados.

    Se voce preencheu so o Telegram, vai so pro Telegram. Se preencheu so o
    Discord, vai so pro Discord. Se preencheu os dois, vai pros dois.
    """
    enviou_algum = False

    if config["telegram_token"] and config["telegram_chat_id"]:
        if enviar_telegram(item, config["telegram_token"], config["telegram_chat_id"]):
            enviou_algum = True

    if config["discord_webhook"]:
        if enviar_discord(item, config["discord_webhook"]):
            enviou_algum = True

    return enviou_algum


# ==========================================================================
#  7. CONFIGURACAO (.env)
# ==========================================================================

def _inteiro_do_ambiente(nome: str, padrao: int) -> int:
    """Le um numero do .env; se estiver vazio ou escrito errado, usa o padrao."""
    bruto = os.getenv(nome, "").strip()
    if not bruto:
        return padrao
    try:
        valor = int(bruto)
    except ValueError:
        log.warning("%s='%s' nao e um numero. Usando %s.", nome, bruto, padrao)
        return padrao
    if valor < 10:
        log.warning("%s=%s e agressivo demais com o site. Usando 10.", nome, valor)
        return 10
    return valor


def _minutos_do_dia(texto: str, padrao: str) -> int:
    """Converte 'HH:MM' em minutos desde a meia-noite. Se vier invalido, usa o padrao."""
    try:
        h, m = texto.strip().split(":")
        h, m = int(h), int(m)
        if not (0 <= h <= 23 and 0 <= m <= 59):
            raise ValueError
        return h * 60 + m
    except (ValueError, AttributeError):
        log.warning("Horario '%s' invalido (use HH:MM). Usando %s.", texto, padrao)
        h, m = padrao.split(":")
        return int(h) * 60 + int(m)


def carregar_config() -> dict:
    """Le o arquivo .env e confere se pelo menos um canal foi configurado."""
    load_dotenv()

    config = {
        "telegram_token": os.getenv("TELEGRAM_BOT_TOKEN", "").strip(),
        "telegram_chat_id": os.getenv("TELEGRAM_CHAT_ID", "").strip(),
        "discord_webhook": os.getenv("DISCORD_WEBHOOK_URL", "").strip(),
        # Vazio = monitora lancamentos de TODAS as abas do site.
        # Preenchido = so daquela aba (ex: 11 para Shoes, 32 para Hoodie).
        "categoria": os.getenv("CATEGORIA_ID", "").strip(),
        # Traduzir os titulos para portugues? (sim por padrao)
        # Desligada por padrao: os titulos vao como o site publica.
        # Para ligar, use TRADUZIR=sim.
        "traduzir": os.getenv("TRADUZIR", "nao").strip().lower()
                    in ("sim", "yes", "1", "true"),
        # E-mail opcional: aumenta a cota diaria gratuita de traducao
        "traducao_email": os.getenv("TRADUCAO_EMAIL", "").strip(),
        # Se preenchido, usa arquivo de texto no lugar do banco SQLite.
        # E o modo usado quando o bot roda hospedado (GitHub Actions).
        "arquivo_estado": os.getenv("ARQUIVO_ESTADO", "").strip(),
        "intervalo": _inteiro_do_ambiente("INTERVALO_SEGUNDOS", INTERVALO_PADRAO),
        # Janela de pico: por padrao 22:00 as 09:00 (horario de Brasilia),
        # rastreando a cada 30s em vez do intervalo normal. Ajustavel sem
        # mexer no codigo — so preencher no Railway/.env.
        "janela_rapida_inicio": _minutos_do_dia(
            os.getenv("JANELA_RAPIDA_INICIO", JANELA_RAPIDA_INICIO_PADRAO),
            JANELA_RAPIDA_INICIO_PADRAO,
        ),
        "janela_rapida_fim": _minutos_do_dia(
            os.getenv("JANELA_RAPIDA_FIM", JANELA_RAPIDA_FIM_PADRAO),
            JANELA_RAPIDA_FIM_PADRAO,
        ),
        "intervalo_rapido": _inteiro_do_ambiente(
            "INTERVALO_RAPIDO_SEGUNDOS", INTERVALO_RAPIDO_PADRAO,
        ),
        "mostrar_real": os.getenv("MOSTRAR_REAL", "nao").strip().lower()
                        in ("sim", "yes", "1", "true"),
    }

    tem_telegram = bool(config["telegram_token"] and config["telegram_chat_id"])
    tem_discord = bool(config["discord_webhook"])

    if not tem_telegram and not tem_discord:
        log.error(
            "Nenhum canal de notificacao configurado!\n"
            "   Abra o arquivo .env e preencha OU o Telegram "
            "(TELEGRAM_BOT_TOKEN + TELEGRAM_CHAT_ID) OU o Discord "
            "(DISCORD_WEBHOOK_URL).\n"
            "   O passo a passo esta no README.md."
        )
        sys.exit(1)

    canais = []
    if tem_telegram:
        canais.append("Telegram")
    if tem_discord:
        canais.append("Discord")
    log.info("Canais ativos: %s", " + ".join(canais))

    if config["categoria"]:
        nome = CATEGORIAS.get(config["categoria"], "categoria " + config["categoria"])
        log.info("Monitorando SOMENTE a aba: %s", nome)
    else:
        log.info("Monitorando lancamentos de TODAS as abas do site.")

    global _mostrar_real
    _mostrar_real = config["mostrar_real"]
    log.info("Precos em Yuan%s.", " + reais" if _mostrar_real else " (CN¥)")

    if config["traduzir"]:
        log.info("Traducao dos titulos para portugues: LIGADA.")
    else:
        log.info("Traducao: desligada — titulos como o site publica.")

    return config


# ==========================================================================
#  8. RODADA DE COLETA
# ==========================================================================

def rodar_coleta(config: dict) -> None:
    """Executa UMA rodada: pergunta os lancamentos, salva e avisa os novos."""
    inicio = time.time()
    log.info("=" * 60)
    log.info("Procurando lancamentos novos em %s", SITE_BASE)

    # Passo 0: pedir licenca ao robots.txt antes de qualquer acesso
    if not robots_permite(API_PRODUTOS):
        return

    conexao = abrir_banco()
    criar_cache_traducao(conexao)
    sessao = criar_sessao()
    primeira_vez = banco_vazio(conexao)

    # Passo 1: buscar os produtos mais recentes na API do site
    paginas, profunda = paginas_desta_rodada(primeira_vez)

    # Reestoque: reconfere, so na varredura profunda (a cada ~20 min), os
    # produtos que ja avisamos antes — se algum esgotou e voltou a vender,
    # avisa de novo.
    caminho_estoque = _caminho_estoque(BANCO_DADOS)
    mapa_estoque = carregar_estoque(caminho_estoque)
    if profunda and mapa_estoque:
        reestocados = verificar_reestoques(sessao, mapa_estoque)
        salvar_estoque(caminho_estoque, mapa_estoque)
        if reestocados:
            log.info("REESTOQUE: %s produto(s) esgotado(s) voltaram a vender.", len(reestocados))
            for item in reestocados:
                item["publicado_em"] = datetime.now(timezone.utc)
                log.info("Avisando REESTOQUE: %s", titulo_visivel(item)[:60])
                notificar(item, config)
                time.sleep(DELAY_ENTRE_MENSAGENS)

    if profunda:
        log.info(
            "Varredura PROFUNDA: lendo %s paginas (~%s produtos) para achar "
            "itens que ficaram visiveis agora mas foram criados ha dias.",
            paginas, paginas * TAMANHO_PAGINA,
        )

    registros = buscar_lancamentos(sessao, config["categoria"], paginas)
    if registros is None:
        log.error("Rodada abortada: nao consegui falar com o site.")
        conexao.close()
        return

    # (Nao ha mais uma pausa extra aqui: a "educacao com o servidor" ja
    # acontece DENTRO de buscar_lancamentos, entre uma pagina e outra.
    # Uma pausa depois que a resposta ja chegou so atrasa voce a toa.)

    # Passo 2: converter para o formato do bot
    itens = extrair_itens(registros)
    log.info("Produtos lidos nesta rodada: %s", len(itens))

    if not itens:
        log.warning(
            "Nenhum produto veio na resposta. Ou o site esta sem novidades, "
            "ou a API mudou — me chame para ajustar."
        )
        conexao.close()
        return

    # Passo 3: PRIMEIRA RODADA — so registra a base, sem notificar.
    # Sem isso voce receberia 50 mensagens de uma vez logo de cara, de
    # produtos que ja estavam no site antes de voce ligar o bot.
    if primeira_vez:
        for item in itens:
            salvar_item(conexao, item, ja_notificado=True)
        conexao.close()
        log.info(
            "PRIMEIRA RODADA: guardei %s produtos como ponto de partida, "
            "sem enviar mensagem.", len(itens),
        )
        log.info(
            "A partir de agora voce so sera avisado do que for LANCADO "
            "depois deste momento. Pode deixar o bot rodando."
        )
        return

    # Passo 4: separar o que e realmente novo
    novos = []
    for item in itens:
        if item_ja_existe(conexao, item["id"]):
            continue
        salvar_item(conexao, item)      # salva na hora (incremental)
        novos.append(item)

    log.info("LANCAMENTOS NOVOS nesta rodada: %s", len(novos))

    # Aviso util: se TODOS os produtos lidos forem novos, e sinal de que
    # sairam mais lancamentos do que o bot consegue ver por rodada.
    if novos and len(novos) == len(itens) and not profunda:
        log.warning(
            "Todos os %s produtos lidos eram novos — pode ter escapado algum. "
            "Se isso repetir, diminua o INTERVALO_SEGUNDOS.", len(itens),
        )

    # Passo 5: notificar tudo que ainda nao foi avisado.
    # Inclui os novos de agora E qualquer atrasado de rodadas anteriores
    # (por exemplo, se o Discord estava fora do ar ou o .env estava errado).
    pendentes = buscar_pendentes(conexao)
    atrasados = len(pendentes) - len(novos)
    if atrasados > 0:
        log.info("Tambem ha %s item(ns) atrasado(s) de rodadas anteriores.", atrasados)

    erros = 0
    if pendentes:
        a_enviar = pendentes[:MAX_NOTIFICACOES_POR_RODADA]
        if len(pendentes) > MAX_NOTIFICACOES_POR_RODADA:
            log.warning(
                "Trava de seguranca: %s itens a avisar, mandando so os %s "
                "primeiros para nao virar spam. O resto ja esta salvo e sera "
                "avisado na proxima rodada.",
                len(pendentes), MAX_NOTIFICACOES_POR_RODADA,
            )

        for numero, item in enumerate(a_enviar, 1):
            # Traduz agora, na hora de enviar — nao antes, em lote (isso
            # atrasaria o item 1 esperando a traducao dos itens 2, 3, 4...)
            if config["traduzir"] and not item.get("titulo_pt"):
                item["titulo_pt"] = traduzir(
                    item["titulo"], conexao, config["traducao_email"]
                )
                conexao.execute(
                    "UPDATE itens SET titulo_pt = ? WHERE id = ?",
                    (item["titulo_pt"], item["id"]),
                )
                conexao.commit()

            # Busca as fotos reais/variacao/link de origem na pagina do
            # produto. Tem timeout curto (TIMEOUT_DETALHE) — se travar ou
            # falhar, segue com a capa mesmo, nunca atrasa o aviso.
            enriquecer_com_detalhes(sessao, item)

            item.setdefault("publicado_em", datetime.now(timezone.utc))

            log.info("Avisando %s/%s: %s", numero, len(a_enviar), titulo_visivel(item)[:60])
            if notificar(item, config):
                marcar_notificado(conexao, item["id"])
                mapa_estoque[item["id"]] = "disponivel"   # entra sob vigilancia de reestoque
            else:
                erros += 1
            # pausa para nao estourar o limite do Telegram (~1 msg/segundo)
            if numero < len(a_enviar):
                time.sleep(DELAY_ENTRE_MENSAGENS)

    salvar_estoque(caminho_estoque, mapa_estoque)
    conexao.close()

    duracao = time.time() - inicio
    log.info(
        "Rodada concluida em %.1fs | lidos: %s | lancamentos novos: %s | "
        "erros de envio: %s", duracao, len(itens), len(novos), erros,
    )


# Momento da ultima varredura profunda (0 = nunca fez)
_ultima_varredura = 0.0


def intervalo_atual(config: dict) -> int:
    """
    Decide quantos segundos esperar ate a proxima rodada.

    Entre a janela de pico configurada (config["janela_rapida_inicio"] a
    config["janela_rapida_fim"], horario de Brasilia — pode atravessar a
    meia-noite, ex: 22:00 as 09:00), usa config["intervalo_rapido"]
    (rastreio mais rapido, ideal pra horario de lancamento). Fora dessa
    janela, usa o intervalo normal (config["intervalo"]).
    """
    agora_brasil = datetime.now(FUSO_HORARIO_JANELA)
    minutos_agora = agora_brasil.hour * 60 + agora_brasil.minute
    inicio, fim = config["janela_rapida_inicio"], config["janela_rapida_fim"]

    # Janela que atravessa a meia-noite (ex: 22:00 as 09:00): esta dentro
    # se for DEPOIS do inicio OU ANTES do fim. Janela normal (ex: 04:00
    # as 09:00): esta dentro se for entre os dois.
    dentro_da_janela = (
        (minutos_agora >= inicio or minutos_agora < fim) if inicio > fim
        else (inicio <= minutos_agora < fim)
    )

    return config["intervalo_rapido"] if dentro_da_janela else config["intervalo"]


def paginas_desta_rodada(primeira_vez: bool) -> tuple:
    """
    Decide se esta rodada le a leitura rapida de rotina ou faz a
    varredura profunda.

    Devolve (quantas_paginas, e_varredura_profunda).

    Na primeira vez SEMPRE varre fundo: e preciso semear a janela inteira,
    senao a primeira varredura acusaria centenas de produtos "novos" que
    na verdade ja existiam.
    """
    global _ultima_varredura

    agora = time.time()
    passou = (agora - _ultima_varredura) >= MINUTOS_ENTRE_VARREDURAS * 60

    if primeira_vez or passou:
        _ultima_varredura = agora
        return PAGINAS_PROFUNDAS, True

    return PAGINAS_RAPIDAS, False


def executar_rodada(config: dict) -> None:
    """Escolhe o modo certo: arquivo de texto (hospedado) ou banco (local)."""
    if config["arquivo_estado"]:
        rodar_coleta_arquivo(config)
    else:
        rodar_coleta(config)


def rodar_coleta_arquivo(config: dict) -> None:
    """
    Rodada no modo hospedado (GitHub Actions).

    Diferenca para o modo local: nao existe banco de dados. A memoria do
    que ja foi avisado e um arquivo de texto com um id por linha, que o
    proprio GitHub versiona entre uma rodada e outra.

    Outra diferenca importante: o id so entra na memoria DEPOIS que a
    mensagem foi enviada com sucesso. Se o envio falhar, o produto continua
    'nao avisado' e entra de novo na proxima rodada — nada se perde.
    """
    inicio = time.time()
    caminho = config["arquivo_estado"]
    caminho_estoque = _caminho_estoque(caminho)
    log.info("=" * 60)
    log.info("Procurando lancamentos novos em %s", SITE_BASE)

    if not robots_permite(API_PRODUTOS):
        return

    ja_vistos = carregar_estado(caminho)
    conjunto = set(ja_vistos)
    primeira_vez = not ja_vistos

    sessao = criar_sessao()
    paginas, profunda = paginas_desta_rodada(primeira_vez)

    # Reestoque: reconfere, so na varredura profunda (a cada ~20 min), os
    # produtos que ja avisamos antes — se algum esgotou e voltou a vender,
    # avisa de novo. So roda na profunda pra nao pesar no site a cada
    # rodada rapida de 15-60s.
    mapa_estoque = carregar_estoque(caminho_estoque)
    if profunda and mapa_estoque:
        reestocados = verificar_reestoques(sessao, mapa_estoque)
        salvar_estoque(caminho_estoque, mapa_estoque)
        if reestocados:
            log.info("REESTOQUE: %s produto(s) esgotado(s) voltaram a vender.", len(reestocados))
            for item in reestocados:
                item["publicado_em"] = datetime.now(timezone.utc)
                log.info("Avisando REESTOQUE: %s", titulo_visivel(item)[:60])
                notificar(item, config)
                time.sleep(DELAY_ENTRE_MENSAGENS)

    if profunda:
        log.info("Varredura PROFUNDA: lendo %s paginas (~%s produtos).",
                 paginas, paginas * TAMANHO_PAGINA)

    registros = buscar_lancamentos(sessao, config["categoria"], paginas)
    if registros is None:
        log.error("Rodada abortada: nao consegui falar com o site.")
        return

    itens = extrair_itens(registros)
    log.info("Produtos lidos nesta rodada: %s", len(itens))
    if not itens:
        log.warning("Nenhum produto veio na resposta.")
        return

    # Primeira vez: so registra a base, sem encher voce de mensagens
    if primeira_vez:
        salvar_estado(caminho, [i["id"] for i in itens])
        log.info(
            "PRIMEIRA RODADA: guardei %s produtos como ponto de partida, "
            "sem enviar mensagem.", len(itens),
        )
        log.info("A partir de agora voce so sera avisado do que for LANCADO depois.")
        return

    # A API devolve do mais novo para o mais antigo; invertemos para avisar
    # na ordem em que os produtos foram publicados.
    novos = [i for i in itens if i["id"] not in conjunto][::-1]
    log.info("LANCAMENTOS NOVOS nesta rodada: %s", len(novos))

    if novos and len(novos) == len(itens):
        log.warning(
            "Todos os %s produtos lidos eram novos — pode ter escapado algum. "
            "Se repetir, aumente TAMANHO_PAGINA ou diminua o intervalo.", len(itens),
        )

    if not novos:
        log.info("Rodada concluida em %.1fs | nada novo.", time.time() - inicio)
        return

    a_enviar = novos[:MAX_NOTIFICACOES_POR_RODADA]
    if len(novos) > MAX_NOTIFICACOES_POR_RODADA:
        log.warning(
            "Trava de seguranca: %s novos, avisando so os %s primeiros. "
            "O resto entra na proxima rodada.",
            len(novos), MAX_NOTIFICACOES_POR_RODADA,
        )

    # Traduz e avisa CADA item na hora, um de cada vez — em vez de traduzir
    # o lote inteiro primeiro e so depois comecar a enviar. Assim o primeiro
    # lancamento chega no Discord sem esperar a traducao dos outros.
    erros = 0
    for numero, item in enumerate(a_enviar, 1):
        if config["traduzir"]:
            item["titulo_pt"] = traduzir(item["titulo"], None, config["traducao_email"])

        # Busca as fotos reais/variacao/link de origem na pagina do
        # produto. Tem timeout curto (TIMEOUT_DETALHE) — se travar ou
        # falhar, segue com a capa mesmo, nunca atrasa o aviso.
        enriquecer_com_detalhes(sessao, item)

        item["publicado_em"] = datetime.now(timezone.utc)
        log.info("Avisando %s/%s: %s", numero, len(a_enviar), titulo_visivel(item)[:60])
        if notificar(item, config):
            ja_vistos.append(item["id"])
            salvar_estado(caminho, ja_vistos)   # grava a cada envio (incremental)
            mapa_estoque[item["id"]] = "disponivel"   # entra sob vigilancia de reestoque
        else:
            erros += 1
        if numero < len(a_enviar):
            time.sleep(DELAY_ENTRE_MENSAGENS)

    salvar_estoque(caminho_estoque, mapa_estoque)

    log.info(
        "Rodada concluida em %.1fs | lidos: %s | novos: %s | erros de envio: %s",
        time.time() - inicio, len(itens), len(novos), erros,
    )


def testar_notificacao(config: dict) -> bool:
    """Manda uma mensagem de teste para conferir se a configuracao esta certa."""
    log.info("Enviando mensagem de TESTE...")
    item_teste = {
        "id": "teste",
        "titulo": "Teste do bot — se voce esta lendo isso, funcionou!",
        "titulo_pt": "",
        "imagem": "",
        "link": "",
        "preco": "",
        "categoria": "",
        "plataforma": "",
        "origem": "",
    }
    if notificar(item_teste, config):
        log.info("SUCESSO! Va conferir no seu grupo — a mensagem chegou.")
        return True

    log.error(
        "Nao consegui enviar. Confira o arquivo .env e as mensagens de "
        "erro acima. O README.md explica como pegar o token e o chat id."
    )
    return False


# ==========================================================================
#  8.5 ASSISTENTE DE CONFIGURACAO  (bot.py --configurar)
# ==========================================================================
#  Faz as perguntas no Terminal e escreve o .env sozinho, para voce nao
#  precisar editar arquivo nenhum na mao.
# ==========================================================================

def _perguntar(rotulo: str) -> str:
    """Pergunta algo no Terminal e devolve a resposta sem espacos sobrando."""
    try:
        return input(rotulo).strip()
    except EOFError:
        return ""


def _gravar_env(valores: dict) -> None:
    """Escreve o arquivo .env e deixa ele legivel so por voce."""
    linhas = [
        "# Gerado pelo assistente (python bot.py --configurar)",
        "# NAO compartilhe este arquivo com ninguem.",
        "",
    ]
    for chave, valor in valores.items():
        linhas.append("{}={}".format(chave, valor))

    with open(".env", "w", encoding="utf-8") as arquivo:
        arquivo.write("\n".join(linhas) + "\n")

    try:
        os.chmod(".env", 0o600)   # so o seu usuario pode ler
    except OSError:
        pass


def _descobrir_chat_id(token: str) -> Optional[str]:
    """
    Descobre sozinho o ID do grupo do Telegram.

    Le as ultimas mensagens que o bot recebeu e pega o grupo de onde elas
    vieram. Por isso e preciso mandar uma mensagem no grupo antes.
    """
    try:
        resposta = requests.get(
            "https://api.telegram.org/bot{}/getUpdates".format(token), timeout=TIMEOUT
        )
        corpo = resposta.json()
    except Exception as erro:
        print("   Nao consegui falar com o Telegram: {}".format(erro))
        return None

    if not corpo.get("ok"):
        print("   O Telegram recusou o token: {}".format(corpo.get("description")))
        return None

    # Procura de tras para frente: o grupo mais recente primeiro
    for atualizacao in reversed(corpo.get("result") or []):
        for campo in ("message", "channel_post", "my_chat_member"):
            chat = (atualizacao.get(campo) or {}).get("chat") or {}
            if chat.get("type") in ("group", "supergroup", "channel"):
                print("   Grupo encontrado: {}".format(chat.get("title") or chat.get("id")))
                return str(chat.get("id"))
    return None


def _gh(*argumentos) -> tuple:
    """Roda um comando do GitHub CLI e devolve (deu_certo, saida)."""
    import subprocess
    caminho = os.path.expanduser("~/.local/bin/gh")
    if not os.path.exists(caminho):
        caminho = "gh"
    try:
        r = subprocess.run(
            [caminho] + list(argumentos),
            capture_output=True, text=True, timeout=60,
        )
        return r.returncode == 0, (r.stdout + r.stderr).strip()
    except FileNotFoundError:
        return False, "GitHub CLI (gh) nao encontrado."
    except Exception as erro:
        return False, str(erro)


def diagnosticar_telegram() -> None:
    """
    Investiga por que o grupo nao foi encontrado e diz exatamente o que fazer.

    Verifica, em ordem: se o token e valido, se ha um webhook atrapalhando,
    se o modo privacidade esta ligado e o que o bot realmente recebeu.
    """
    print()
    print("=" * 64)
    print("  DIAGNOSTICO DO TELEGRAM")
    print("=" * 64)

    token = _perguntar("\n  Cole o token do @BotFather: ")
    if ":" not in token or len(token) < 20:
        print("  Isso nao parece um token do Telegram.")
        return

    base = "https://api.telegram.org/bot{}".format(token)

    def chamar(metodo):
        try:
            return requests.get("{}/{}".format(base, metodo), timeout=TIMEOUT).json()
        except Exception as erro:
            return {"ok": False, "description": str(erro)}

    # ---- 1. o token funciona? ----
    print()
    print("  [1] Conferindo o token...")
    eu = chamar("getMe")
    if not eu.get("ok"):
        print("      X TOKEN INVALIDO: {}".format(eu.get("description")))
        print("      Copie o token de novo do @BotFather (inteiro, sem espacos).")
        return

    dados = eu["result"]
    print("      OK - bot: @{} ({})".format(dados.get("username"), dados.get("first_name")))
    print("      pode ser adicionado a grupos: {}".format(
        "sim" if dados.get("can_join_groups") else "NAO"))
    print("      le mensagens comuns de grupo: {}".format(
        "sim" if dados.get("can_read_all_group_messages") else "NAO (modo privacidade LIGADO)"))

    # ---- 2. tem webhook atrapalhando? ----
    print()
    print("  [2] Conferindo se ha webhook configurado...")
    webhook = chamar("getWebhookInfo")
    url_webhook = (webhook.get("result") or {}).get("url") or ""
    if url_webhook:
        print("      X TEM UM WEBHOOK ATIVO: {}".format(url_webhook[:60]))
        print("      Enquanto ele existir, o bot NAO consegue ler as mensagens.")
        print("      Remova abrindo este endereco no navegador:")
        print("      {}/deleteWebhook".format(base))
        return
    print("      OK - nenhum webhook atrapalhando")

    # ---- 3. o que o bot recebeu? ----
    print()
    print("  [3] Vendo o que o bot recebeu...")
    atualizacoes = chamar("getUpdates")
    if not atualizacoes.get("ok"):
        print("      X {}".format(atualizacoes.get("description")))
        return

    lista = atualizacoes.get("result") or []
    print("      {} evento(s) recebido(s)".format(len(lista)))

    grupos = {}
    for item in lista:
        for campo, conteudo in item.items():
            if not isinstance(conteudo, dict):
                continue
            chat = conteudo.get("chat") or {}
            if chat.get("id"):
                print("        - {}: chat '{}' (tipo {})".format(
                    campo, chat.get("title") or chat.get("first_name"), chat.get("type")))
                if chat.get("type") in ("group", "supergroup", "channel"):
                    grupos[str(chat["id"])] = chat.get("title")

    # ---- veredito ----
    print()
    print("=" * 64)
    if grupos:
        print("  ENCONTRADO!")
        for ident, titulo in grupos.items():
            print("     {}  ->  {}".format(titulo, ident))

        # ---- teste de envio de verdade ----
        print()
        print("  [4] Mandando uma mensagem de TESTE agora...")
        print()
        algum_ok = False
        for ident, titulo in grupos.items():
            ok = enviar_telegram(
                {"titulo": "Teste do bot — se voce esta lendo isso, "
                           "o envio funciona!",
                 "titulo_pt": "", "imagem": "", "link": "", "preco": "",
                 "categoria": "", "plataforma": ""},
                token, ident,
            )
            if ok:
                algum_ok = True
                print("      ENVIADO para '{}' — va conferir!".format(titulo))
            else:
                print("      FALHOU em '{}' (veja o erro acima).".format(titulo))
                print("      Causa mais comum: o grupo/canal so deixa")
                print("      administradores escreverem e o bot nao e admin.")

        print()
        print("=" * 64)
        if algum_ok:
            print("  A MENSAGEM CHEGOU? Entao token, ID e permissao estao OK.")
            print()
            print("  Use estes valores no Railway (aba Variables):")
            for ident in grupos:
                print("     TELEGRAM_CHAT_ID = {}".format(ident))
        else:
            print("  NAO CONSEGUI ENVIAR. O bot nao vai funcionar assim,")
            print("  nem no Railway. Corrija a permissao e rode de novo.")
        return
    else:
        print("  NENHUM GRUPO ENCONTRADO. O que fazer:")
        print()
        if not dados.get("can_read_all_group_messages"):
            print("  CAUSA MAIS PROVAVEL: modo privacidade ligado.")
            print("  Bots do @BotFather nascem sem poder ler mensagens comuns")
            print("  de grupo — so mensagens que comecam com barra ( / ).")
            print()
            print("  SOLUCAO RAPIDA (10 segundos):")
            print("     Mande  /start  no grupo. Mensagens com barra sempre")
            print("     chegam ao bot, mesmo com o modo privacidade ligado.")
            print()
            print("  SOLUCAO DEFINITIVA (se preferir):")
            print("     No @BotFather mande /setprivacy, escolha @{}".format(
                dados.get("username")))
            print("     e clique em Disable. Depois REMOVA e ADICIONE o bot")
            print("     no grupo de novo (a mudanca so vale ao reentrar).")
        else:
            print("  O modo privacidade ja esta desligado, entao confira:")
            print("     - o bot @{} esta MESMO nesse grupo?".format(dados.get("username")))
            print("     - voce mandou a mensagem DEPOIS de adicionar ele?")
            print("     - o token e desse bot mesmo (nao de outro que voce criou)?")
        print()
        print("  Depois disso, rode este diagnostico de novo.")
    print("=" * 64)


def configurar_github() -> None:
    """
    Guarda o token do Telegram (ou o webhook do Discord) no cofre do GitHub.

    Tudo acontece na SUA maquina: voce digita o token aqui, ele vai direto
    para o cofre do GitHub e nao fica salvo em arquivo nenhum.
    """
    print()
    print("=" * 64)
    print("  GUARDAR AS SENHAS NO COFRE DO GITHUB")
    print("=" * 64)

    ok, saida = _gh("auth", "status")
    if not ok:
        print()
        print("  Voce ainda nao autorizou o GitHub CLI.")
        print("  Rode primeiro:  ~/.local/bin/gh auth login --web")
        return

    repo = _perguntar("\n  Qual o repositorio? (ex: seu-usuario/bot-cssdeals): ")
    if "/" not in repo:
        print("  Formato invalido. Precisa ser usuario/repositorio.")
        return

    print()
    print("  Onde voce quer receber os avisos?")
    print("    1 - Telegram")
    print("    2 - Discord")
    escolha = _perguntar("  Digite 1 ou 2: ")

    # ------------------------------- TELEGRAM ------------------------------
    if escolha == "1":
        print()
        print("  Passo 1: pegue o token com o @BotFather no Telegram")
        print("           (mande /newbot e siga as perguntas)")
        print()
        token = _perguntar("  Cole o token aqui: ")
        if ":" not in token or len(token) < 20:
            print("  Isso nao parece um token do Telegram.")
            return

        print()
        print("  Passo 2: antes de continuar, confirme que voce ja:")
        print("     a) criou o grupo no Telegram")
        print("     b) adicionou o SEU bot nesse grupo")
        print("     c) mandou qualquer mensagem no grupo (ex: 'oi')")
        print()
        _perguntar("  Feito? Aperte Enter para eu procurar o grupo... ")

        chat_id = _descobrir_chat_id(token)
        if not chat_id:
            print()
            print("  Nao achei nenhum grupo.")
            print("  O mais comum: faltou mandar uma mensagem no grupo DEPOIS")
            print("  de adicionar o bot. Faca isso e rode este comando de novo.")
            return

        print()
        print("  Enviando uma mensagem de teste antes de salvar...")
        if not enviar_telegram(
            {"titulo": "Teste do bot — funcionou!", "titulo_pt": "", "imagem": "",
             "link": "", "preco": "", "categoria": "", "plataforma": ""},
            token, chat_id,
        ):
            print()
            print("  A mensagem de teste NAO chegou. Nao vou salvar nada.")
            print("  Confira se o bot esta mesmo no grupo e tente de novo.")
            return

        print("  Mensagem de teste enviada! Confira o grupo.")
        print()
        print("  Salvando no cofre do GitHub...")
        segredos = {"TELEGRAM_BOT_TOKEN": token, "TELEGRAM_CHAT_ID": chat_id}

    # ------------------------------- DISCORD -------------------------------
    elif escolha == "2":
        print()
        url = _perguntar("  Cole a URL do webhook do Discord: ")
        if "discord.com/api/webhooks/" not in url and \
           "discordapp.com/api/webhooks/" not in url:
            print("  Isso nao parece a URL de um webhook do Discord.")
            return

        print()
        print("  Enviando uma mensagem de teste antes de salvar...")
        if not enviar_discord(
            {"titulo": "Teste do bot — funcionou!", "titulo_pt": "", "imagem": "",
             "link": "", "preco": "", "categoria": "", "plataforma": ""}, url,
        ):
            print()
            print("  A mensagem de teste NAO chegou. Nao vou salvar nada.")
            return

        print("  Mensagem de teste enviada! Confira o canal.")
        print()
        print("  Salvando no cofre do GitHub...")
        segredos = {"DISCORD_WEBHOOK_URL": url}

    else:
        print("  Opcao invalida.")
        return

    # --------------------------- gravar no cofre ---------------------------
    for nome, valor in segredos.items():
        ok, saida = _gh("secret", "set", nome, "--repo", repo, "--body", valor)
        if ok:
            print("     {} ....... guardado".format(nome))
        else:
            print("     {} ....... FALHOU: {}".format(nome, saida[:120]))
            return

    print()
    print("=" * 64)
    print("  TUDO PRONTO!")
    print()
    print("  O bot ja esta no ar. Ele roda sozinho na nuvem do GitHub;")
    print("  seu computador pode ficar desligado.")
    print()
    print("  A primeira rodada guarda os produtos atuais sem avisar.")
    print("  Da segunda em diante chegam so os lancamentos novos.")
    print("=" * 64)


def assistente_configuracao() -> None:
    """Conversa com voce no Terminal e monta o .env do zero."""
    print()
    print("=" * 64)
    print("  ASSISTENTE DE CONFIGURACAO")
    print("=" * 64)

    if os.path.exists(".env"):
        if _perguntar("Ja existe um .env. Quer refazer? (s/n): ").lower() not in ("s", "sim"):
            print("Nada foi alterado.")
            return

    print()
    print("  Onde voce quer receber os avisos?")
    print("    1 - Discord   (mais facil: 4 cliques, sem criar bot)")
    print("    2 - Telegram")
    escolha = _perguntar("  Digite 1 ou 2: ")

    valores = {"TRADUZIR": "nao", "TRADUCAO_EMAIL": "", "CATEGORIA_ID": ""}

    # ------------------------------- DISCORD -------------------------------
    if escolha == "1":
        print()
        print("  Como pegar a URL (no app do Discord):")
        print("    1. Passe o mouse no canal que vai receber os avisos")
        print("    2. Clique na engrenagem (Editar Canal)")
        print("    3. Menu da esquerda: Integracoes -> Webhooks -> Novo webhook")
        print("    4. Clique em 'Copiar URL do Webhook'")
        print()

        url = _perguntar("  Cole a URL aqui e aperte Enter: ")
        if not url.startswith("https://discord.com/api/webhooks/") and \
           not url.startswith("https://discordapp.com/api/webhooks/"):
            print()
            print("  Isso nao parece a URL de um webhook do Discord.")
            print("  Ela precisa comecar com https://discord.com/api/webhooks/")
            return

        valores["DISCORD_WEBHOOK_URL"] = url
        valores["TELEGRAM_BOT_TOKEN"] = ""
        valores["TELEGRAM_CHAT_ID"] = ""

    # ------------------------------- TELEGRAM ------------------------------
    elif escolha == "2":
        print()
        print("  Como pegar o token:")
        print("    1. No Telegram, procure @BotFather (tem selo azul)")
        print("    2. Mande /newbot e siga as perguntas")
        print("    3. Ele responde com o token (algo como 123456:AAH...)")
        print()

        token = _perguntar("  Cole o token aqui e aperte Enter: ")
        if ":" not in token or len(token) < 20:
            print()
            print("  Isso nao parece um token do Telegram.")
            return

        print()
        print("  Agora preciso descobrir o ID do grupo. Antes de continuar:")
        print("    1. Crie o grupo (se ainda nao criou)")
        print("    2. Adicione o seu bot ao grupo")
        print("    3. Mande QUALQUER mensagem no grupo (ex: 'oi')")
        print()
        _perguntar("  Feito isso, aperte Enter para eu procurar... ")

        chat_id = _descobrir_chat_id(token)
        if not chat_id:
            print()
            print("  Nao achei nenhum grupo.")
            print("  Confirme que o bot foi adicionado E que voce mandou uma")
            print("  mensagem no grupo depois disso. Depois rode de novo:")
            print("      .venv/bin/python bot.py --configurar")
            return

        valores["TELEGRAM_BOT_TOKEN"] = token
        valores["TELEGRAM_CHAT_ID"] = chat_id
        valores["DISCORD_WEBHOOK_URL"] = ""

    else:
        print("  Opcao invalida. Rode de novo e digite 1 ou 2.")
        return

    # ------------------------- gravar e testar -----------------------------
    _gravar_env(valores)
    print()
    print("  Arquivo .env gravado. Mandando uma mensagem de teste...")
    print()

    load_dotenv(override=True)
    config = {
        "telegram_token": valores.get("TELEGRAM_BOT_TOKEN", ""),
        "telegram_chat_id": valores.get("TELEGRAM_CHAT_ID", ""),
        "discord_webhook": valores.get("DISCORD_WEBHOOK_URL", ""),
    }
    deu_certo = testar_notificacao(config)

    print()
    print("=" * 64)
    if deu_certo:
        print("  TUDO PRONTO! A mensagem de teste chegou no seu grupo.")
        print()
        print("  O agendador ja esta ligado e roda a cada 15 minutos.")
        print("  A primeira rodada guarda os produtos atuais sem avisar;")
        print("  depois disso voce recebe so os lancamentos novos.")
    else:
        print("  A CONFIGURACAO FOI SALVA, MAS O TESTE NAO PASSOU.")
        print()
        print("  Veja a mensagem de erro logo acima — ela diz o motivo.")
        print("  O mais comum e a URL/token ter sido copiado pela metade.")
        print()
        print("  Para tentar de novo:")
        print("      .venv/bin/python bot.py --configurar")
    print("=" * 64)


# ==========================================================================
#  9. PONTO DE ENTRADA
# ==========================================================================

def main() -> None:
    leitor = argparse.ArgumentParser(
        description="Bot de coleta com notificacao no Telegram/Discord."
    )
    leitor.add_argument(
        "--loop", action="store_true",
        help="Roda sem parar (intervalo pelo INTERVALO_SEGUNDOS do .env).",
    )
    leitor.add_argument(
        "--configurar", action="store_true",
        help="Assistente que pergunta os dados e monta o .env sozinho.",
    )
    leitor.add_argument(
        "--configurar-github", dest="configurar_github", action="store_true",
        help="Guarda o token/webhook no cofre do GitHub (para rodar hospedado).",
    )
    leitor.add_argument(
        "--diagnosticar-telegram", dest="diag_telegram", action="store_true",
        help="Descobre por que o grupo do Telegram nao foi encontrado.",
    )
    leitor.add_argument(
        "--testar", action="store_true",
        help="So envia uma mensagem de teste e sai (nao coleta nada).",
    )
    leitor.add_argument(
        "--buscar", metavar="TERMO",
        help="Procura produtos pelo titulo e mostra todas as fotos (nao envia nada).",
    )
    leitor.add_argument(
        "--testar-rede", dest="testar_rede", action="store_true",
        help="Confere se este servidor alcanca cssdeals/Telegram/Discord (IPv4 e IPv6).",
    )
    argumentos = leitor.parse_args()

    if argumentos.testar_rede:
        testar_rede()
        return

    if argumentos.buscar:
        comando_buscar(argumentos.buscar)
        return

    # O assistente roda ANTES da checagem de configuracao — e justamente
    # ele que cria o .env que a checagem exige.
    if argumentos.configurar:
        assistente_configuracao()
        return

    if argumentos.configurar_github:
        configurar_github()
        return

    if argumentos.diag_telegram:
        diagnosticar_telegram()
        return

    config = carregar_config()

    if argumentos.testar:
        if not testar_notificacao(config):
            sys.exit(1)
        return

    if argumentos.loop:
        _fmt_hhmm = lambda minutos: "{:02d}:{:02d}".format(minutos // 60, minutos % 60)
        log.info(
            "MODO CONTINUO ligado — verificando a cada %s segundos "
            "(entre %s e %s, horario de Brasilia, verifica a cada "
            "%s segundos).",
            config["intervalo"],
            _fmt_hhmm(config["janela_rapida_inicio"]),
            _fmt_hhmm(config["janela_rapida_fim"]),
            config["intervalo_rapido"],
        )

        janela_rapida_ativa_antes = False
        while True:
            try:
                executar_rodada(config)
            except Exception as erro:
                # Blindagem final: nada derruba o loop
                log.exception("Erro inesperado na rodada: %s", erro)

            espera = intervalo_atual(config)

            janela_rapida_ativa = espera == config["intervalo_rapido"]
            if janela_rapida_ativa != janela_rapida_ativa_antes:
                if janela_rapida_ativa:
                    log.info(
                        "Entrando na janela rapida (%s-%s): rastreio a cada %ss.",
                        _fmt_hhmm(config["janela_rapida_inicio"]),
                        _fmt_hhmm(config["janela_rapida_fim"]), espera,
                    )
                else:
                    log.info(
                        "Saindo da janela rapida: rastreio volta a cada %ss.",
                        espera,
                    )
                janela_rapida_ativa_antes = janela_rapida_ativa

            time.sleep(espera)
    else:
        executar_rodada(config)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        log.info("\nBot encerrado por voce. Ate mais!")
        sys.exit(0)
