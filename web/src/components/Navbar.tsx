import Link from 'next/link'
import { ThemeToggle } from './ThemeToggle'

/** Top navigation bar — gives the site a normal-website feel. */
export function Navbar() {
  return (
    <nav className="h-14 shrink-0 flex items-center px-8 border-b border-white/10 bg-[#0a0a0f]/80 backdrop-blur relative z-20">
      <a
        href="https://astrolabe.network/"
        className="text-sm font-semibold tracking-[0.22em] text-white/85 hover:text-white transition-colors"
      >
        ASTROLABE
      </a>
      <div className="ml-auto flex items-center gap-6 text-xs text-white/40">
        <a href="https://astrolabe.network/" className="hover:text-white/75 transition-colors">
          Home
        </a>
        <Link href="/docs/challenge" className="hover:text-white/75 transition-colors">
          About us
        </Link>
        <a
          href="https://github.com/MathNetwork/OpenGA"
          target="_blank"
          rel="noopener noreferrer"
          aria-label="GitHub"
          title="GitHub"
          className="hover:text-white/75 transition-colors"
        >
          <svg width="18" height="18" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
            <path d="M12 .297c-6.63 0-12 5.373-12 12 0 5.303 3.438 9.8 8.205 11.385.6.113.82-.258.82-.577 0-.285-.01-1.04-.015-2.04-3.338.724-4.042-1.61-4.042-1.61C4.422 18.07 3.633 17.7 3.633 17.7c-1.087-.744.084-.729.084-.729 1.205.084 1.838 1.236 1.838 1.236 1.07 1.835 2.809 1.305 3.495.998.108-.776.417-1.305.76-1.605-2.665-.3-5.466-1.332-5.466-5.93 0-1.31.465-2.38 1.235-3.22-.135-.303-.54-1.523.105-3.176 0 0 1.005-.322 3.3 1.23.96-.267 1.98-.399 3-.405 1.02.006 2.04.138 3 .405 2.28-1.552 3.285-1.23 3.285-1.23.645 1.653.24 2.873.12 3.176.765.84 1.23 1.91 1.23 3.22 0 4.61-2.805 5.625-5.475 5.92.42.36.81 1.096.81 2.22 0 1.606-.015 2.896-.015 3.286 0 .315.21.69.825.57C20.565 22.092 24 17.592 24 12.297c0-6.627-5.373-12-12-12" />
          </svg>
        </a>
        <a
          href="https://discord.gg/CvfrT34ra"
          target="_blank"
          rel="noopener noreferrer"
          aria-label="Join our Discord"
          title="Join our Discord"
          className="hover:text-white/75 transition-colors"
        >
          <svg width="22" height="18" viewBox="0 0 127.14 96.36" fill="currentColor" aria-hidden="true">
            <path d="M107.7 8.07A105.15 105.15 0 0 0 81.47 0a72.06 72.06 0 0 0-3.36 6.83 97.68 97.68 0 0 0-29.11 0A72.37 72.37 0 0 0 45.64 0a105.89 105.89 0 0 0-26.25 8.09C2.79 32.65-1.71 56.6.54 80.21a105.73 105.73 0 0 0 32.17 16.15 77.7 77.7 0 0 0 6.89-11.11 68.42 68.42 0 0 1-10.85-5.18c.91-.66 1.8-1.34 2.66-2a75.57 75.57 0 0 0 64.32 0c.87.71 1.76 1.39 2.66 2a68.68 68.68 0 0 1-10.87 5.19 77 77 0 0 0 6.89 11.1 105.25 105.25 0 0 0 32.19-16.14c2.64-27.38-4.51-51.11-18.9-72.15ZM42.45 65.69C36.18 65.69 31 60 31 53s5-12.74 11.43-12.74S54 46 53.89 53s-5.05 12.69-11.44 12.69Zm42.24 0C78.41 65.69 73.25 60 73.25 53s5-12.74 11.44-12.74S96.23 46 96.12 53s-5.04 12.69-11.43 12.69Z" />
          </svg>
        </a>
        <ThemeToggle className="hover:text-white/75 transition-colors" />
      </div>
    </nav>
  )
}
