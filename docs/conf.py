# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

project = 'Differential Geometry in Lean'
copyright = '2025, Jens Lindekamp'
author = 'Jens Lindekamp'
release = '0.1'


# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration

highlight_language = "lean"

templates_path = ['_templates']
exclude_patterns = ['_build']


# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

html_theme = 'karma-sphinx-theme'
html_static_path = ['_static']

# -- Options for LaTeX output ---------------------------------------------

latex_engine = 'xelatex'

latex_additional_files = ['unixode.sty']

latex_elements = {
    # The paper size ('letterpaper' or 'a4paper').
    #
    # 'papersize': 'letterpaper',

    # The font size ('10pt', '11pt' or '12pt').
    #
    # 'pointsize': '10pt',

    # Additional stuff for the LaTeX preamble.
   # load packages and make box around code lighter
    'preamble': r'''
\usepackage{unixode}
\definecolor{VerbatimBorderColor}{rgb}{0.7,0.7,0.7}
% from sphinxmanual.cls: put authors on separate lines
\DeclareRobustCommand{\and}{%
   \end{tabular}\kern-\tabcolsep\\\begin{tabular}[t]{c}%
}
''',

    # Latex figure (float) alignment
    #
    # 'figure_align': 'htbp',
}
