'use client'

import { useEffect, useState } from 'react'
import { SunIcon, MoonIcon } from '@heroicons/react/24/outline'

/** Global day/night toggle. Light mode is a CSS inverse-colour overlay applied to
 *  <html> (see globals.css); the choice is persisted to localStorage. */
export function ThemeToggle({ className }: { className?: string }) {
  const [light, setLight] = useState(false)

  useEffect(() => {
    setLight(document.documentElement.classList.contains('light'))
  }, [])

  const toggle = () => {
    const next = !document.documentElement.classList.contains('light')
    document.documentElement.classList.toggle('light', next)
    try { localStorage.setItem('theme', next ? 'light' : 'dark') } catch { /* ignore */ }
    setLight(next)
  }

  return (
    <button
      onClick={toggle}
      title={light ? 'Switch to dark mode' : 'Switch to light mode'}
      className={className ?? 'hover:text-white/75 transition-colors'}
    >
      {light ? <MoonIcon className="w-4 h-4" /> : <SunIcon className="w-4 h-4" />}
    </button>
  )
}
